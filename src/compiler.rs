use {
  super::*,
  inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    types::BasicTypeEnum,
    values::{
      BasicMetadataValueEnum, BasicValueEnum, FunctionValue, PointerValue,
    },
  },
  std::collections::HashMap,
};

#[derive(Debug)]
pub struct Compiler<'ctx> {
  context: &'ctx Context,
  module: Module<'ctx>,
  builder: Builder<'ctx>,
  symbols: HashMap<String, PointerValue<'ctx>>,
  pointer_type_map: HashMap<PointerValue<'ctx>, BasicTypeEnum<'ctx>>,
  current_function: Option<FunctionValue<'ctx>>,
}

impl<'ctx> Compiler<'ctx> {
  pub fn new(context: &'ctx Context) -> Self {
    let module = context.create_module(env!("CARGO_PKG_NAME"));

    let builder = context.create_builder();

    Self {
      builder,
      context,
      current_function: None,
      module,
      pointer_type_map: HashMap::new(),
      symbols: HashMap::new(),
    }
  }

  pub fn compile(
    &mut self,
    expressions: &[Expression],
  ) -> Result<Module<'ctx>> {
    self.register_builtins()?;

    let functions = expressions
      .iter()
      .filter(|expr| expr.is_function())
      .collect::<Vec<&Expression>>();

    for function in &functions {
      self.compile_expression(function)?;
    }

    let i32_type = self.context.i32_type();

    let function =
      self
        .module
        .add_function("main", i32_type.fn_type(&[], false), None);

    let basic_block = self.context.append_basic_block(function, "entry");

    self.builder.position_at_end(basic_block);

    self.current_function = Some(function);

    let mut result = None;

    let expressions = expressions
      .iter()
      .filter(|expression| !functions.contains(expression))
      .collect::<Vec<&Expression>>();

    for expression in &expressions {
      result = Some(self.compile_expression(expression)?);
    }

    let return_value = match result {
      Some(val) => self.cast_to_i32(val),
      None => i32_type.const_int(0, false),
    };

    self
      .builder
      .build_return(Some(&return_value))
      .map_err(|e| e.to_string())?;

    Ok(self.module.clone())
  }

  fn register_builtins(&mut self) -> Result<(), String> {
    let primitives = [
      ("*", 2),
      ("+", 2),
      ("-", 2),
      ("/", 2),
      ("<", 2),
      ("=", 2),
      (">", 2),
      ("display", 2),
    ];

    for (primitive, arity) in primitives {
      let i64_type = self.context.i64_type();

      let global = self.module.add_global(i64_type, None, primitive);
      global.set_initializer(&i64_type.const_int(arity as u64, false));

      let ptr = global.as_pointer_value();
      self.symbols.insert(primitive.to_string(), ptr);
      self.pointer_type_map.insert(ptr, i64_type.into());
    }

    self.module.add_function(
      "printf",
      self.context.i32_type().fn_type(
        &[self.context.ptr_type(AddressSpace::default()).into()],
        true,
      ),
      None,
    );

    Ok(())
  }

  fn compile_expression(
    &mut self,
    expr: &Expression,
  ) -> Result<BasicValueEnum<'ctx>> {
    match expr {
      Expression::Atom(atom) => self.compile_atom(atom),
      Expression::List(elements) => self.compile_list(elements),
      _ => todo!(),
    }
  }

  fn compile_atom(&self, atom: &Atom) -> Result<BasicValueEnum<'ctx>> {
    match atom {
      Atom::Boolean(b) => {
        Ok(self.context.bool_type().const_int(*b as u64, false).into())
      }
      Atom::Number(number) => self.compile_number(number),
      Atom::String(s) => Ok(
        self
          .builder
          .build_global_string_ptr(s, "string_const")
          .map_err(|e| e.to_string())?
          .as_pointer_value()
          .into(),
      ),
      Atom::Character(c) => {
        Ok(self.context.i8_type().const_int(*c as u64, false).into())
      }
      Atom::Symbol(s) => {
        if let Some(val) = self.symbols.get(*s) {
          Ok((*val).into())
        } else {
          Err(format!("Undefined symbol `{}`", s).into())
        }
      }
    }
  }

  fn compile_number(&self, num: &Number) -> Result<BasicValueEnum<'ctx>> {
    match num {
      Number::Integer(i) => {
        Ok(self.context.i64_type().const_int(*i as u64, *i < 0).into())
      }
      Number::Float(f) => Ok(self.context.f64_type().const_float(*f).into()),
      Number::Rational(_, _) => todo!(),
      Number::Complex(_, _) => Err("Complex numbers not yet supported".into()),
      Number::Unparsed(s) => {
        Err(format!("Could not parse number: {}", s).into())
      }
    }
  }

  fn compile_list(
    &mut self,
    elements: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    if elements.is_empty() {
      return Ok(self.context.i32_type().const_int(0, false).into());
    }

    match &elements[0] {
      Expression::Atom(Atom::Symbol(name)) => match *name {
        "*" => self.compile_primitive_operation("*", &elements[1..]),
        "+" => self.compile_primitive_operation("+", &elements[1..]),
        "-" => self.compile_primitive_operation("-", &elements[1..]),
        "/" => self.compile_primitive_operation("/", &elements[1..]),
        "<" => self.compile_primitive_operation("<", &elements[1..]),
        "=" => self.compile_primitive_operation("=", &elements[1..]),
        ">" => self.compile_primitive_operation(">", &elements[1..]),
        "begin" => self.compile_begin(&elements[1..]),
        "define" => self.compile_define(&elements[1..]),
        "display" => self.compile_display(&elements[1..]),
        "if" => self.compile_if(&elements[1..]),
        "lambda" => todo!(),
        "let" => todo!(),
        "newline" => self.compile_newline(&elements[1..]),
        _ => self.compile_function_call(name, &elements[1..]),
      },
      _ => todo!(),
    }
  }

  fn compile_newline(
    &mut self,
    arguments: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    if !arguments.is_empty() {
      return Err("Function `newline` does not accept any arguments".into());
    }

    let printf = self
      .module
      .get_function("printf")
      .ok_or("Printf function not found".to_string())?;

    let newline_format = self
      .builder
      .build_global_string_ptr("\n", "newline_format")
      .map_err(|e| e.to_string())?;

    self
      .builder
      .build_call(
        printf,
        &[newline_format.as_pointer_value().into()],
        "printf_newline",
      )
      .map_err(|e| e.to_string())?;

    Ok(self.context.i32_type().const_int(0, false).into())
  }

  fn compile_primitive_operation(
    &mut self,
    operation: &str,
    arguments: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    let compiled_arguments = arguments
      .iter()
      .map(|argument| self.compile_expression(argument))
      .collect::<Result<Vec<_>, _>>()?;

    if compiled_arguments.is_empty() {
      return Err(
        format!("Primitive operation {operation} requires arguments").into(),
      );
    }

    match operation {
      "+" => {
        let argument = self.dereference(compiled_arguments[0])?;

        match argument {
          BasicValueEnum::IntValue(i) => {
            let mut int_result = i;

            for argument in &compiled_arguments[1..] {
              match self.dereference(*argument)? {
                BasicValueEnum::IntValue(i) => {
                  int_result = self
                    .builder
                    .build_int_add(int_result, i, "add")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in addition".into()),
              }
            }

            Ok(int_result.into())
          }
          BasicValueEnum::FloatValue(f) => {
            let mut float_result = f;

            for argument in &compiled_arguments[1..] {
              match argument {
                BasicValueEnum::FloatValue(f) => {
                  float_result = self
                    .builder
                    .build_float_add(float_result, *f, "add")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in addition".into()),
              }
            }

            Ok(float_result.into())
          }
          _ => Err("Unsupported type for addition".into()),
        }
      }
      "-" => {
        if compiled_arguments.len() == 1 {
          let argument = self.dereference(compiled_arguments[0])?;

          match argument {
            BasicValueEnum::IntValue(i) => {
              let zero = self.context.i64_type().const_int(0, false);

              let result = self
                .builder
                .build_int_sub(zero, i, "neg")
                .map_err(|e| e.to_string())?;

              Ok(result.into())
            }
            BasicValueEnum::FloatValue(f) => {
              let zero = self.context.f64_type().const_float(0.0);

              let result = self
                .builder
                .build_float_sub(zero, f, "neg")
                .map_err(|e| e.to_string())?;

              Ok(result.into())
            }
            _ => Err(
              format!("Unsupported type for negation: {:?}", argument).into(),
            ),
          }
        } else {
          let argument = self.dereference(compiled_arguments[0])?;

          match argument {
            BasicValueEnum::IntValue(i) => {
              let mut int_result = i;

              for argument in &compiled_arguments[1..] {
                let argument_value = self.dereference(*argument)?;

                match argument_value {
                  BasicValueEnum::IntValue(i) => {
                    int_result = self
                      .builder
                      .build_int_sub(int_result, i, "sub")
                      .map_err(|e| e.to_string())?;
                  }
                  _ => {
                    return Err(format!(
                      "Type mismatch in subtraction, expected integer, got: {:?}",
                      argument_value
                    ).into());
                  }
                }
              }

              Ok(int_result.into())
            }
            BasicValueEnum::FloatValue(f) => {
              let mut float_result = f;

              for argument in &compiled_arguments[1..] {
                let argument_value = self.dereference(*argument)?;

                match argument_value {
                  BasicValueEnum::FloatValue(f) => {
                    float_result = self
                      .builder
                      .build_float_sub(float_result, f, "sub")
                      .map_err(|e| e.to_string())?;
                  }
                  _ => {
                    return Err(format!(
                      "Type mismatch in subtraction, expected float, got: {:?}",
                      argument_value
                    ).into());
                  }
                }
              }

              Ok(float_result.into())
            }
            _ => Err(
              format!("Unsupported type for subtraction: {:?}", argument)
                .into(),
            ),
          }
        }
      }
      "*" => {
        if compiled_arguments.is_empty() {
          return Err("Multiplication requires at least one argument".into());
        }

        let first = self.dereference(compiled_arguments[0])?;

        match first {
          BasicValueEnum::IntValue(i) => {
            let mut int_result = i;

            for argument in &compiled_arguments[1..] {
              let argument_value = self.dereference(*argument)?;

              match argument_value {
                BasicValueEnum::IntValue(i) => {
                  int_result = self
                    .builder
                    .build_int_mul(int_result, i, "mul")
                    .map_err(|e| e.to_string())?;
                }
                _ => {
                  return Err(format!(
                    "Type mismatch in multiplication, expected integer, got: {:?}",
                    argument_value
                  ).into());
                }
              }
            }

            Ok(int_result.into())
          }
          BasicValueEnum::FloatValue(f) => {
            let mut float_result = f;

            for argument in &compiled_arguments[1..] {
              let argument_value = self.dereference(*argument)?;

              match argument_value {
                BasicValueEnum::FloatValue(f) => {
                  float_result = self
                    .builder
                    .build_float_mul(float_result, f, "mul")
                    .map_err(|e| e.to_string())?;
                }
                _ => {
                  return Err(format!(
                    "Type mismatch in multiplication, expected float, got: {:?}",
                    argument_value
                  ).into());
                }
              }
            }

            Ok(float_result.into())
          }
          _ => Err(
            format!("Unsupported type for multiplication: {:?}", first).into(),
          ),
        }
      }
      "/" => {
        let argument = compiled_arguments[0];

        match argument {
          BasicValueEnum::IntValue(i) => {
            let mut int_result = i;

            for argument in &compiled_arguments[1..] {
              match argument {
                BasicValueEnum::IntValue(i) => {
                  int_result = self
                    .builder
                    .build_int_signed_div(int_result, *i, "div")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in division".into()),
              }
            }

            Ok(int_result.into())
          }
          BasicValueEnum::FloatValue(f) => {
            let mut float_result = f;

            for argument in &compiled_arguments[1..] {
              match argument {
                BasicValueEnum::FloatValue(f) => {
                  float_result = self
                    .builder
                    .build_float_div(float_result, *f, "div")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in division".into()),
              }
            }

            Ok(float_result.into())
          }
          _ => Err("Unsupported type for division".into()),
        }
      }
      "=" => {
        if compiled_arguments.len() != 2 {
          return Err(
            "Equality comparison requires exactly 2 arguments".into(),
          );
        }

        let (lhs, rhs) = (
          self.dereference(compiled_arguments[0])?,
          self.dereference(compiled_arguments[1])?,
        );

        match (lhs, rhs) {
          (BasicValueEnum::IntValue(i1), BasicValueEnum::IntValue(i2)) => Ok(
            self
              .builder
              .build_int_compare(inkwell::IntPredicate::EQ, i1, i2, "eq")
              .map_err(|e| e.to_string())?
              .into(),
          ),
          (BasicValueEnum::FloatValue(f1), BasicValueEnum::FloatValue(f2)) => {
            Ok(
              self
                .builder
                .build_float_compare(inkwell::FloatPredicate::OEQ, f1, f2, "eq")
                .map_err(|e| e.to_string())?
                .into(),
            )
          }
          _ => Err(format!(
            "Type mismatch in equality comparison after loading: lhs={:?}, rhs={:?}",
            lhs, rhs
          ).into()),
        }
      }
      "<" => {
        if compiled_arguments.len() != 2 {
          return Err(
            "Less than comparison requires exactly 2 arguments".into(),
          );
        }

        let (lhs, rhs) = (
          self.dereference(compiled_arguments[0])?,
          self.dereference(compiled_arguments[1])?,
        );

        match (lhs, rhs) {
          (BasicValueEnum::IntValue(i1), BasicValueEnum::IntValue(i2)) => Ok(
            self
              .builder
              .build_int_compare(inkwell::IntPredicate::SLT, i1, i2, "lt")
              .map_err(|e| e.to_string())?
              .into(),
          ),
          (BasicValueEnum::FloatValue(f1), BasicValueEnum::FloatValue(f2)) => {
            Ok(
              self
                .builder
                .build_float_compare(inkwell::FloatPredicate::OLT, f1, f2, "lt")
                .map_err(|e| e.to_string())?
                .into(),
            )
          }
          _ => Err(
            format!(
              "Type mismatch in less than comparison: lhs={:?}, rhs={:?}",
              lhs, rhs
            )
            .into(),
          ),
        }
      }
      ">" => {
        if compiled_arguments.len() != 2 {
          return Err(
            "Greater than comparison requires exactly 2 arguments".into(),
          );
        }

        let (lhs, rhs) = (
          self.dereference(compiled_arguments[0])?,
          self.dereference(compiled_arguments[1])?,
        );

        match (lhs, rhs) {
          (BasicValueEnum::IntValue(i1), BasicValueEnum::IntValue(i2)) => Ok(
            self
              .builder
              .build_int_compare(inkwell::IntPredicate::SGT, i1, i2, "gt")
              .map_err(|e| e.to_string())?
              .into(),
          ),
          (BasicValueEnum::FloatValue(f1), BasicValueEnum::FloatValue(f2)) => {
            Ok(
              self
                .builder
                .build_float_compare(inkwell::FloatPredicate::OGT, f1, f2, "gt")
                .map_err(|e| e.to_string())?
                .into(),
            )
          }
          _ => Err(format!(
            "Type mismatch in greater than comparison after loading: lhs={:?}, rhs={:?}",
            lhs, rhs
          ).into()),
        }
      }
      "display" => self.compile_display(arguments),
      _ => Err(format!("Unknown primitive operation: {}", operation).into()),
    }
  }

  fn dereference(
    &self,
    value: BasicValueEnum<'ctx>,
  ) -> Result<BasicValueEnum<'ctx>> {
    match value {
      BasicValueEnum::PointerValue(ptr) => {
        if let Some(pointee_type) = self.pointer_type_map.get(&ptr) {
          Ok(self.builder.build_load(*pointee_type, ptr, "typed_load")?)
        } else {
          Err("Failed to find type for pointer".into())
        }
      }
      _ => Ok(value),
    }
  }

  fn compile_if(
    &mut self,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    if args.len() < 2 || args.len() > 3 {
      return Err("If expression requires 2 or 3 arguments".into());
    }

    let condition = self.compile_expression(&args[0])?;

    let condition_value = match condition {
      BasicValueEnum::IntValue(val) => val,
      BasicValueEnum::PointerValue(ptr) => {
        let i64_type = self.context.i64_type();

        match self
          .builder
          .build_load(i64_type, ptr, "load_condition")
          .map_err(|e| e.to_string())?
        {
          BasicValueEnum::IntValue(val) => val,
          _ => return Err("Condition must be a boolean value".into()),
        }
      }
      _ => return Err("Condition must be a boolean value".into()),
    };

    let condition_bool = self
      .builder
      .build_int_truncate_or_bit_cast(
        condition_value,
        self.context.bool_type(),
        "if_bool",
      )
      .map_err(|e| e.to_string())?;

    let current_function = self
      .current_function
      .ok_or("No current function for if expression".to_string())?;

    let then_block = self.context.append_basic_block(current_function, "then");

    let else_block = self.context.append_basic_block(current_function, "else");

    let merge_block =
      self.context.append_basic_block(current_function, "merge");

    self
      .builder
      .build_conditional_branch(condition_bool, then_block, else_block)
      .map_err(|e| e.to_string())?;

    self.builder.position_at_end(then_block);

    let then_value = self.compile_expression(&args[1])?;

    let then_block = self.builder.get_insert_block().unwrap();

    self
      .builder
      .build_unconditional_branch(merge_block)
      .map_err(|e| e.to_string())?;

    self.builder.position_at_end(else_block);

    let else_value = if args.len() == 3 {
      self.compile_expression(&args[2])?
    } else {
      self.context.i32_type().const_int(0, false).into()
    };

    let else_block = self.builder.get_insert_block().unwrap();

    self
      .builder
      .build_unconditional_branch(merge_block)
      .map_err(|e| e.to_string())?;

    self.builder.position_at_end(merge_block);

    if then_value.get_type() == else_value.get_type() {
      let phi = self
        .builder
        .build_phi(then_value.get_type(), "if_result")
        .map_err(|e| e.to_string())?;

      phi.add_incoming(&[(&then_value, then_block), (&else_value, else_block)]);

      Ok(phi.as_basic_value())
    } else {
      Ok(else_value)
    }
  }

  fn compile_define(
    &mut self,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    if args.len() != 2 {
      return Err("Define requires exactly 2 arguments".into());
    }

    match &args[0] {
      Expression::Atom(Atom::Symbol(name)) => {
        let value = self.compile_expression(&args[1])?;

        let global_type = match value {
          BasicValueEnum::IntValue(_) => self.context.i64_type().into(),
          BasicValueEnum::FloatValue(_) => self.context.f64_type().into(),
          _ => self.context.i64_type().into(),
        };

        let global = self.module.add_global(global_type, None, name);

        match value {
          BasicValueEnum::IntValue(i) => {
            if global_type == self.context.i64_type().into() {
              global.set_initializer(&i);
            } else {
              let casted = self
                .builder
                .build_int_cast(i, self.context.i64_type(), "cast_to_i64")
                .map_err(|e| e.to_string())?;
              global.set_initializer(&casted);
            }
          }
          BasicValueEnum::FloatValue(f) => {
            if global_type == self.context.f64_type().into() {
              global.set_initializer(&f);
            } else {
              let converted = self
                .builder
                .build_float_to_signed_int(
                  f,
                  self.context.i64_type(),
                  "float_to_i64",
                )
                .map_err(|e| e.to_string())?;
              global.set_initializer(&converted);
            }
          }
          _ => return Err("Unsupported type for global variable".into()),
        };

        let ptr = global.as_pointer_value();
        self.symbols.insert((*name).to_string(), ptr);
        self.pointer_type_map.insert(ptr, global_type);

        Ok(self.context.i32_type().const_int(0, false).into())
      }
      Expression::List(func_def) => {
        if func_def.is_empty() {
          return Err("Function definition requires a name".into());
        }

        if let Expression::Atom(Atom::Symbol(name)) = &func_def[0] {
          let params: Vec<&str> = func_def[1..]
            .iter()
            .filter_map(|expr| {
              if let Expression::Atom(Atom::Symbol(param)) = expr {
                Some(*param)
              } else {
                None
              }
            })
            .collect();

          let i64_type = self.context.i64_type();

          let function = self.module.add_function(
            name,
            i64_type.fn_type(&vec![i64_type.into(); params.len()], false),
            None,
          );

          let ptr = function.as_global_value().as_pointer_value();
          self.symbols.insert((*name).to_string(), ptr);

          let old_function = self.current_function;
          self.current_function = Some(function);

          let entry_block = self.context.append_basic_block(function, "entry");
          self.builder.position_at_end(entry_block);

          let old_symbols = self.symbols.clone();
          let old_type_map = self.pointer_type_map.clone();

          for (i, name) in params.iter().enumerate() {
            let parameter = function
              .get_nth_param(i as u32)
              .ok_or(format!("Failed to get parameter {}", i))?;

            let alloca = self
              .builder
              .build_alloca(parameter.get_type(), name)
              .map_err(|e| e.to_string())?;

            self
              .builder
              .build_store(alloca, parameter)
              .map_err(|e| e.to_string())?;

            self.symbols.insert((*name).to_string(), alloca);

            self.pointer_type_map.insert(alloca, parameter.get_type());
          }

          let body_result = self.compile_expression(&args[1])?;

          let return_value = match body_result {
            BasicValueEnum::FloatValue(f) => self
              .builder
              .build_float_to_signed_int(f, i64_type, "float_to_i64_return")
              .map_err(|e| e.to_string())?
              .into(),
            _ => body_result,
          };

          self
            .builder
            .build_return(Some(&return_value))
            .map_err(|e| e.to_string())?;

          self.symbols = old_symbols;
          self.pointer_type_map = old_type_map;

          self.current_function = old_function;

          Ok(self.context.i32_type().const_int(0, false).into())
        } else {
          Err("Function name must be a symbol".into())
        }
      }
      _ => Err("First argument to define must be a symbol or a list".into()),
    }
  }

  fn compile_function_call(
    &mut self,
    name: &str,
    arguments: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    let arguments = arguments
      .iter()
      .map(|arg| self.compile_expression(arg))
      .collect::<Result<Vec<_>, _>>()?;

    let function = self
      .module
      .get_function(name)
      .ok_or(format!("Function not found: {}", name))?;

    if function.count_params() != arguments.len() as u32 {
      return Err(
        format!(
          "Function {} expects {} argument(s), but got {}",
          name,
          function.count_params(),
          arguments.len()
        )
        .into(),
      );
    }

    let mut processed_arguments = Vec::with_capacity(arguments.len());

    for (i, argument) in arguments.iter().enumerate() {
      let parameter = function.get_nth_param(i as u32).ok_or(format!(
        "Failed to get parameter {} of function {}",
        i, name
      ))?;

      let param_type = parameter.get_type();
      let mut processed_argument = self.dereference(*argument)?;

      match (processed_argument, param_type) {
        (BasicValueEnum::FloatValue(f), BasicTypeEnum::IntType(int_ty)) => {
          processed_argument = self
            .builder
            .build_float_to_signed_int(
              f,
              int_ty,
              &format!("float_to_int_{}", i),
            )
            .map_err(|e| e.to_string())?
            .into();
        }
        (BasicValueEnum::IntValue(i), BasicTypeEnum::FloatType(float_ty)) => {
          processed_argument = self
            .builder
            .build_signed_int_to_float(
              i,
              float_ty,
              &format!("int_to_float_{}", i),
            )
            .map_err(|e| e.to_string())?
            .into();
        }
        (BasicValueEnum::IntValue(i), BasicTypeEnum::IntType(int_ty)) => {
          if i.get_type() != int_ty {
            processed_argument = self
              .builder
              .build_int_cast(i, int_ty, &format!("int_cast_{}", i))
              .map_err(|e| e.to_string())?
              .into();
          }
        }
        _ => {}
      }

      processed_arguments.push(processed_argument);
    }

    let arguments = processed_arguments
      .into_iter()
      .map(BasicMetadataValueEnum::from)
      .collect::<Vec<BasicMetadataValueEnum>>();

    let result = self
      .builder
      .build_call(function, arguments.as_slice(), "call")
      .map_err(|e| e.to_string())?
      .try_as_basic_value()
      .left()
      .ok_or(format!("Function {} does not return a value", name))?;

    Ok(result)
  }

  fn compile_display(
    &mut self,
    arguments: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    if arguments.len() != 1 {
      return Err("Function `display` requires exactly 1 argument".into());
    }

    let value = self.compile_expression(&arguments[0])?;

    let printf = self
      .module
      .get_function("printf")
      .ok_or("Failed to find printf function".to_string())?;

    let format_string = match value {
      BasicValueEnum::IntValue(_) => self
        .builder
        .build_global_string_ptr("%ld", "int_format")
        .map_err(|e| e.to_string())?,
      BasicValueEnum::FloatValue(_) => self
        .builder
        .build_global_string_ptr("%f", "float_format")
        .map_err(|e| e.to_string())?,
      BasicValueEnum::PointerValue(_) => self
        .builder
        .build_global_string_ptr("%s", "string_format")
        .map_err(|e| e.to_string())?,
      _ => return Err("Unsupported type for display".into()),
    };

    self
      .builder
      .build_call(
        printf,
        &[format_string.as_pointer_value().into(), value.into()],
        "printf_call",
      )
      .map_err(|e| e.to_string())?;

    Ok(value)
  }

  fn compile_begin(
    &mut self,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>> {
    if args.is_empty() {
      return Ok(self.context.i32_type().const_int(0, false).into());
    }

    let mut result = None;

    for expr in args {
      result = Some(self.compile_expression(expr)?);
    }

    Ok(result.unwrap())
  }

  fn cast_to_i32(
    &self,
    value: BasicValueEnum<'ctx>,
  ) -> inkwell::values::IntValue<'ctx> {
    match value {
      BasicValueEnum::IntValue(v) => {
        if v.get_type() == self.context.i32_type() {
          v
        } else {
          self
            .builder
            .build_int_cast(v, self.context.i32_type(), "toi32")
            .expect("Failed to build int cast")
        }
      }
      BasicValueEnum::FloatValue(v) => self
        .builder
        .build_float_to_signed_int(v, self.context.i32_type(), "toi32")
        .expect("Failed to build float to int cast"),
      _ => self.context.i32_type().const_int(0, false),
    }
  }
}

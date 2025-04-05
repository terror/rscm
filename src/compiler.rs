use {
  super::*,
  inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    values::{
      BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue,
      PointerValue,
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
  current_function: Option<FunctionValue<'ctx>>,
}

impl<'ctx> Compiler<'ctx> {
  pub fn new(context: &'ctx Context, module_name: &str) -> Self {
    let module = context.create_module(module_name);

    let builder = context.create_builder();

    Self {
      context,
      module,
      builder,
      symbols: HashMap::new(),
      current_function: None,
    }
  }

  pub fn compile(&mut self, expressions: &[Expression]) -> Result<(), String> {
    self.declare_stdlib_functions();
    self.initialize_global_env();

    for expr in expressions {
      if let Expression::List(elements) = expr {
        if !elements.is_empty() {
          if let Expression::Atom(Atom::Symbol(name)) = &elements[0] {
            if *name == "define" {
              self.compile_expression(expr)?;
            }
          }
        }
      }
    }

    let i32_type = self.context.i32_type();

    let fn_type = i32_type.fn_type(&[], false);

    let function = self.module.add_function("main", fn_type, None);

    let basic_block = self.context.append_basic_block(function, "entry");

    self.builder.position_at_end(basic_block);
    self.current_function = Some(function);

    let mut result = None;

    for expr in expressions {
      if let Expression::List(elements) = expr {
        if !elements.is_empty() {
          if let Expression::Atom(Atom::Symbol(name)) = &elements[0] {
            if *name != "define" {
              result = Some(self.compile_expression(expr)?);
            }
          }
        }
      } else {
        result = Some(self.compile_expression(expr)?);
      }
    }

    let return_value = match result {
      Some(val) => self.cast_to_i32(val),
      None => i32_type.const_int(0, false),
    };

    self
      .builder
      .build_return(Some(&return_value))
      .map_err(|e| e.to_string())?;

    if self.module.verify().is_err() {
      self.module.print_to_stderr();
      return Err("Failed to verify module".to_string());
    }

    Ok(())
  }

  pub fn get_ir(&self) -> String {
    self.module.print_to_string().to_string()
  }

  fn declare_stdlib_functions(&self) {
    let i8_ptr_type = self.context.ptr_type(AddressSpace::default());

    let printf_type =
      self.context.i32_type().fn_type(&[i8_ptr_type.into()], true);

    self.module.add_function("printf", printf_type, None);
  }

  fn initialize_global_env(&mut self) {
    self.define_primitive("+", 2);
    self.define_primitive("-", 2);
    self.define_primitive("*", 2);
    self.define_primitive("/", 2);
    self.define_primitive("=", 2);
    self.define_primitive("<", 2);
    self.define_primitive(">", 2);
    self.define_primitive("display", 1);
  }

  fn define_primitive(&mut self, name: &str, arity: u32) {
    let i64_type = self.context.i64_type();

    let global = self.module.add_global(i64_type, None, name);

    global.set_initializer(&i64_type.const_int(arity as u64, false));

    self
      .symbols
      .insert(name.to_string(), global.as_pointer_value());
  }

  fn compile_expression(
    &mut self,
    expr: &Expression,
  ) -> Result<BasicValueEnum<'ctx>, String> {
    match expr {
      Expression::Atom(atom) => self.compile_atom(atom),
      Expression::List(elements) => self.compile_list(elements),
      _ => todo!(),
    }
  }

  fn compile_atom(&self, atom: &Atom) -> Result<BasicValueEnum<'ctx>, String> {
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
          Err(format!("Undefined symbol: {}", s))
        }
      }
    }
  }

  fn compile_number(
    &self,
    num: &Number,
  ) -> Result<BasicValueEnum<'ctx>, String> {
    match num {
      Number::Integer(i) => {
        let val = self.context.i64_type().const_int(*i as u64, *i < 0);
        Ok(val.into())
      }
      Number::Float(f) => {
        let val = self.context.f64_type().const_float(*f);
        Ok(val.into())
      }
      Number::Rational(num, denom) => {
        let num_val = self.context.i64_type().const_int(*num as u64, *num < 0);

        let denom_val =
          self.context.i64_type().const_int(*denom as u64, *denom < 0);

        let float_num = self
          .builder
          .build_signed_int_to_float(
            num_val,
            self.context.f64_type(),
            "float_num",
          )
          .map_err(|e| e.to_string())?;

        let float_denom = self
          .builder
          .build_signed_int_to_float(
            denom_val,
            self.context.f64_type(),
            "float_denom",
          )
          .map_err(|e| e.to_string())?;

        let result = self
          .builder
          .build_float_div(float_num, float_denom, "rational_div")
          .map_err(|e| e.to_string())?;

        Ok(result.into())
      }
      Number::Complex(_, _) => {
        Err("Complex numbers not yet supported".to_string())
      }
      Number::Unparsed(s) => Err(format!("Could not parse number: {}", s)),
    }
  }

  fn compile_list(
    &mut self,
    elements: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>, String> {
    if elements.is_empty() {
      return Ok(self.context.i32_type().const_int(0, false).into());
    }

    match &elements[0] {
      Expression::Atom(Atom::Symbol(name)) => match *name {
        "define" => self.compile_define(&elements[1..]),
        "if" => self.compile_if(&elements[1..]),
        "lambda" => todo!(),
        "let" => todo!(),
        "begin" => self.compile_begin(&elements[1..]),
        "+" => self.compile_primitive_op("+", &elements[1..]),
        "-" => self.compile_primitive_op("-", &elements[1..]),
        "*" => self.compile_primitive_op("*", &elements[1..]),
        "/" => self.compile_primitive_op("/", &elements[1..]),
        "=" => self.compile_primitive_op("=", &elements[1..]),
        "<" => self.compile_primitive_op("<", &elements[1..]),
        ">" => self.compile_primitive_op(">", &elements[1..]),
        "display" => self.compile_display(&elements[1..]),
        _ => self.compile_function_call(name, &elements[1..]),
      },
      _ => todo!(),
    }
  }

  fn compile_primitive_op(
    &mut self,
    op: &str,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>, String> {
    let compiled_args: Result<Vec<_>, _> = args
      .iter()
      .map(|arg| self.compile_expression(arg))
      .collect();

    let compiled_args = compiled_args?;

    if compiled_args.is_empty() {
      return Err(format!("Primitive operation {} requires arguments", op));
    }

    match op {
      "+" => {
        let result = compiled_args[0];

        match result {
          BasicValueEnum::IntValue(i) => {
            let mut int_result = i;
            for arg in &compiled_args[1..] {
              match arg {
                BasicValueEnum::IntValue(i) => {
                  int_result = self
                    .builder
                    .build_int_add(int_result, *i, "add")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in addition".to_string()),
              }
            }
            Ok(int_result.into())
          }
          BasicValueEnum::FloatValue(f) => {
            let mut float_result = f;
            for arg in &compiled_args[1..] {
              match arg {
                BasicValueEnum::FloatValue(f) => {
                  float_result = self
                    .builder
                    .build_float_add(float_result, *f, "add")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in addition".to_string()),
              }
            }
            Ok(float_result.into())
          }
          _ => Err("Unsupported type for addition".to_string()),
        }
      }
      "-" => {
        let dereference = |value: BasicValueEnum<'ctx>| -> Result<BasicValueEnum<'ctx>, String> {
        match value {
            BasicValueEnum::PointerValue(ptr) => {
                let i64_type = self.context.i64_type();
                self.builder
                    .build_load(i64_type, ptr, "dereferenced")
                    .map_err(|e| e.to_string())
            }
            _ => Ok(value),
        }
    };

        if compiled_args.len() == 1 {
          let arg = dereference(compiled_args[0])?;

          match arg {
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
            _ => Err(format!("Unsupported type for negation: {:?}", arg)),
          }
        } else {
          let first = dereference(compiled_args[0])?;

          match first {
            BasicValueEnum::IntValue(i) => {
              let mut int_result = i;
              for arg in &compiled_args[1..] {
                let arg_val = dereference(*arg)?;

                match arg_val {
                  BasicValueEnum::IntValue(i) => {
                    int_result = self
                      .builder
                      .build_int_sub(int_result, i, "sub")
                      .map_err(|e| e.to_string())?;
                  }
                  _ => {
                    return Err(format!(
                      "Type mismatch in subtraction, expected integer, got: {:?}",
                      arg_val
                    ));
                  }
                }
              }
              Ok(int_result.into())
            }
            BasicValueEnum::FloatValue(f) => {
              let mut float_result = f;
              for arg in &compiled_args[1..] {
                let arg_val = dereference(*arg)?;

                match arg_val {
                  BasicValueEnum::FloatValue(f) => {
                    float_result = self
                      .builder
                      .build_float_sub(float_result, f, "sub")
                      .map_err(|e| e.to_string())?;
                  }
                  _ => {
                    return Err(format!(
                      "Type mismatch in subtraction, expected float, got: {:?}",
                      arg_val
                    ));
                  }
                }
              }
              Ok(float_result.into())
            }
            _ => Err(format!("Unsupported type for subtraction: {:?}", first)),
          }
        }
      }
      "*" => {
        let dereference = |value: BasicValueEnum<'ctx>| -> Result<BasicValueEnum<'ctx>, String> {
          match value {
            BasicValueEnum::PointerValue(ptr) => {
              let i64_type = self.context.i64_type();

              self.builder
                .build_load(i64_type, ptr, "dereferenced")
                .map_err(|e| e.to_string())
            }
            _ => Ok(value),
          }
        };

        if compiled_args.is_empty() {
          return Err(
            "Multiplication requires at least one argument".to_string(),
          );
        }

        let first = dereference(compiled_args[0])?;

        match first {
          BasicValueEnum::IntValue(i) => {
            let mut int_result = i;
            for arg in &compiled_args[1..] {
              let arg_val = dereference(*arg)?;

              match arg_val {
                BasicValueEnum::IntValue(i) => {
                  int_result = self
                    .builder
                    .build_int_mul(int_result, i, "mul")
                    .map_err(|e| e.to_string())?;
                }
                _ => {
                  return Err(format!(
                    "Type mismatch in multiplication, expected integer, got: {:?}",
                    arg_val
                  ));
                }
              }
            }
            Ok(int_result.into())
          }
          BasicValueEnum::FloatValue(f) => {
            let mut float_result = f;
            for arg in &compiled_args[1..] {
              let arg_val = dereference(*arg)?;

              match arg_val {
                BasicValueEnum::FloatValue(f) => {
                  float_result = self
                    .builder
                    .build_float_mul(float_result, f, "mul")
                    .map_err(|e| e.to_string())?;
                }
                _ => {
                  return Err(format!(
                    "Type mismatch in multiplication, expected float, got: {:?}",
                    arg_val
                  ));
                }
              }
            }
            Ok(float_result.into())
          }
          _ => Err(format!("Unsupported type for multiplication: {:?}", first)),
        }
      }
      "/" => {
        let result = compiled_args[0];

        match result {
          BasicValueEnum::IntValue(i) => {
            let mut int_result = i;
            for arg in &compiled_args[1..] {
              match arg {
                BasicValueEnum::IntValue(i) => {
                  int_result = self
                    .builder
                    .build_int_signed_div(int_result, *i, "div")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in division".to_string()),
              }
            }
            Ok(int_result.into())
          }
          BasicValueEnum::FloatValue(f) => {
            let mut float_result = f;
            for arg in &compiled_args[1..] {
              match arg {
                BasicValueEnum::FloatValue(f) => {
                  float_result = self
                    .builder
                    .build_float_div(float_result, *f, "div")
                    .map_err(|e| e.to_string())?;
                }
                _ => return Err("Type mismatch in division".to_string()),
              }
            }
            Ok(float_result.into())
          }
          _ => Err("Unsupported type for division".to_string()),
        }
      }
      "=" => {
        if compiled_args.len() != 2 {
          return Err(
            "Equality comparison requires exactly 2 arguments".to_string(),
          );
        }

        let mut lhs = compiled_args[0];
        let mut rhs = compiled_args[1];

        if let BasicValueEnum::PointerValue(ptr) = lhs {
          let i64_type = self.context.i64_type();
          lhs = self
            .builder
            .build_load(i64_type, ptr, "load_lhs")
            .map_err(|e| e.to_string())?;
        }

        if let BasicValueEnum::PointerValue(ptr) = rhs {
          let i64_type = self.context.i64_type();
          rhs = self
            .builder
            .build_load(i64_type, ptr, "load_rhs")
            .map_err(|e| e.to_string())?;
        }

        match (lhs, rhs) {
          (BasicValueEnum::IntValue(i1), BasicValueEnum::IntValue(i2)) => {
            let i1_type = i1.get_type();
            let i2_type = i2.get_type();

            let i1_cast = if i1_type != i2_type {
              self
                .builder
                .build_int_cast(i1, i2_type, "cast_lhs")
                .map_err(|e| e.to_string())?
            } else {
              i1
            };

            let result = self
              .builder
              .build_int_compare(inkwell::IntPredicate::EQ, i1_cast, i2, "eq")
              .map_err(|e| e.to_string())?;

            Ok(result.into())
          }
          (BasicValueEnum::FloatValue(f1), BasicValueEnum::FloatValue(f2)) => {
            let result = self
              .builder
              .build_float_compare(inkwell::FloatPredicate::OEQ, f1, f2, "eq")
              .map_err(|e| e.to_string())?;

            Ok(result.into())
          }
          _ => Err(format!(
            "Type mismatch in equality comparison after loading: lhs={:?}, rhs={:?}",
            lhs, rhs
          )),
        }
      }
      "<" => {
        if compiled_args.len() != 2 {
          return Err(
            "Less than comparison requires exactly 2 arguments".to_string(),
          );
        }

        let mut lhs = compiled_args[0];
        let mut rhs = compiled_args[1];

        if let BasicValueEnum::PointerValue(ptr) = lhs {
          let i64_type = self.context.i64_type();
          lhs = self
            .builder
            .build_load(i64_type, ptr, "load_lhs")
            .map_err(|e| e.to_string())?;
        }

        if let BasicValueEnum::PointerValue(ptr) = rhs {
          let i64_type = self.context.i64_type();
          rhs = self
            .builder
            .build_load(i64_type, ptr, "load_rhs")
            .map_err(|e| e.to_string())?;
        }

        match (lhs, rhs) {
          (BasicValueEnum::IntValue(i1), BasicValueEnum::IntValue(i2)) => {
            let result = self
              .builder
              .build_int_compare(inkwell::IntPredicate::SLT, i1, i2, "lt")
              .map_err(|e| e.to_string())?;

            Ok(result.into())
          }
          (BasicValueEnum::FloatValue(f1), BasicValueEnum::FloatValue(f2)) => {
            let result = self
              .builder
              .build_float_compare(inkwell::FloatPredicate::OLT, f1, f2, "lt")
              .map_err(|e| e.to_string())?;

            Ok(result.into())
          }
          _ => Err(format!(
            "Type mismatch in less than comparison: lhs={:?}, rhs={:?}",
            lhs, rhs
          )),
        }
      }
      ">" => {
        if compiled_args.len() != 2 {
          return Err(
            "Greater than comparison requires exactly 2 arguments".to_string(),
          );
        }

        let mut lhs = compiled_args[0];
        let mut rhs = compiled_args[1];

        if let BasicValueEnum::PointerValue(ptr) = lhs {
          let i64_type = self.context.i64_type();

          lhs = self
            .builder
            .build_load(i64_type, ptr, "load_lhs")
            .map_err(|e| e.to_string())?;
        }

        if let BasicValueEnum::PointerValue(ptr) = rhs {
          let i64_type = self.context.i64_type();

          rhs = self
            .builder
            .build_load(i64_type, ptr, "load_rhs")
            .map_err(|e| e.to_string())?;
        }

        match (lhs, rhs) {
          (BasicValueEnum::IntValue(i1), BasicValueEnum::IntValue(i2)) => {
            let i1_type = i1.get_type();
            let i2_type = i2.get_type();

            let i1_cast = if i1_type != i2_type {
              self
                .builder
                .build_int_cast(i1, i2_type, "cast_lhs")
                .map_err(|e| e.to_string())?
            } else {
              i1
            };

            let result = self
              .builder
              .build_int_compare(inkwell::IntPredicate::SGT, i1_cast, i2, "gt")
              .map_err(|e| e.to_string())?;

            Ok(result.into())
          }
          (BasicValueEnum::FloatValue(f1), BasicValueEnum::FloatValue(f2)) => {
            let result = self
              .builder
              .build_float_compare(inkwell::FloatPredicate::OGT, f1, f2, "gt")
              .map_err(|e| e.to_string())?;

            Ok(result.into())
          }
          _ => Err(format!(
            "Type mismatch in greater than comparison after loading: lhs={:?}, rhs={:?}",
            lhs, rhs
          )),
        }
      }
      "display" => self.compile_display(args),
      _ => Err(format!("Unknown primitive operation: {}", op)),
    }
  }

  fn compile_if(
    &mut self,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>, String> {
    if args.len() < 2 || args.len() > 3 {
      return Err("If expression requires 2 or 3 arguments".to_string());
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
          _ => return Err("Condition must be a boolean value".to_string()),
        }
      }
      _ => return Err("Condition must be a boolean value".to_string()),
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
  ) -> Result<BasicValueEnum<'ctx>, String> {
    if args.len() != 2 {
      return Err("Define requires exactly 2 arguments".to_string());
    }

    match &args[0] {
      Expression::Atom(Atom::Symbol(name)) => {
        let value = self.compile_expression(&args[1])?;

        let i64_type = self.context.i64_type();

        let global = self.module.add_global(i64_type, None, name);

        let value_i64 = match value {
          BasicValueEnum::IntValue(i) => {
            if i.get_type() == i64_type {
              i
            } else {
              self
                .builder
                .build_int_cast(i, i64_type, "cast_to_i64")
                .map_err(|e| e.to_string())?
            }
          }
          BasicValueEnum::FloatValue(f) => self
            .builder
            .build_float_to_signed_int(f, i64_type, "float_to_i64")
            .map_err(|e| e.to_string())?,
          _ => return Err("Unsupported type for global variable".to_string()),
        };

        global.set_initializer(&value_i64);

        self
          .symbols
          .insert((*name).to_string(), global.as_pointer_value());

        Ok(self.context.i32_type().const_int(0, false).into())
      }
      Expression::List(func_def) => {
        if func_def.is_empty() {
          return Err("Function definition requires a name".to_string());
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
          let param_types = vec![i64_type.into(); params.len()];
          let fn_type = i64_type.fn_type(&param_types, false);

          let function = self.module.add_function(name, fn_type, None);

          self.symbols.insert(
            (*name).to_string(),
            function.as_global_value().as_pointer_value(),
          );

          let old_function = self.current_function;
          self.current_function = Some(function);

          let entry_block = self.context.append_basic_block(function, "entry");
          self.builder.position_at_end(entry_block);

          let old_symbols = self.symbols.clone();

          for (i, param_name) in params.iter().enumerate() {
            let param = function
              .get_nth_param(i as u32)
              .ok_or(format!("Failed to get parameter {}", i))?;

            let alloca = self
              .builder
              .build_alloca(param.get_type(), param_name)
              .map_err(|e| e.to_string())?;

            self
              .builder
              .build_store(alloca, param)
              .map_err(|e| e.to_string())?;

            self.symbols.insert((*param_name).to_string(), alloca);
          }

          let body_result = self.compile_expression(&args[1])?;

          self
            .builder
            .build_return(Some(&body_result))
            .map_err(|e| e.to_string())?;

          self.symbols = old_symbols;
          self.current_function = old_function;

          Ok(self.context.i32_type().const_int(0, false).into())
        } else {
          Err("Function name must be a symbol".to_string())
        }
      }
      _ => {
        Err("First argument to define must be a symbol or a list".to_string())
      }
    }
  }

  fn compile_function_call(
    &mut self,
    name: &str,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>, String> {
    let compiled_args: Result<Vec<_>, _> = args
      .iter()
      .map(|arg| self.compile_expression(arg))
      .collect();

    let compiled_args = compiled_args?;

    let function = self
      .module
      .get_function(name)
      .ok_or(format!("Function not found: {}", name))?;

    if function.count_params() != compiled_args.len() as u32 {
      return Err(format!(
        "Function {} expects {} arguments, but got {}",
        name,
        function.count_params(),
        compiled_args.len()
      ));
    }

    let mut processed_args = Vec::with_capacity(compiled_args.len());

    for (i, arg) in compiled_args.iter().enumerate() {
      let param = function.get_nth_param(i as u32).ok_or(format!(
        "Failed to get parameter {} of function {}",
        i, name
      ))?;

      let mut processed_arg = *arg;

      if let BasicValueEnum::PointerValue(ptr) = processed_arg {
        let i64_type = self.context.i64_type();
        processed_arg = self
          .builder
          .build_load(i64_type, ptr, &format!("load_arg_{}", i))
          .map_err(|e| e.to_string())?;
      }

      if let (
        BasicValueEnum::IntValue(i),
        BasicValueEnum::IntValue(expected_i),
      ) = (processed_arg, param.as_basic_value_enum())
      {
        if i.get_type() != expected_i.get_type() {
          processed_arg = self
            .builder
            .build_int_cast(
              i,
              expected_i.get_type(),
              &format!("cast_arg_{}", i),
            )
            .map_err(|e| e.to_string())?
            .into();
        }
      }

      processed_args.push(processed_arg);
    }

    let args = processed_args
      .into_iter()
      .map(|arg| BasicMetadataValueEnum::from(arg))
      .collect::<Vec<BasicMetadataValueEnum>>();

    let result = self
      .builder
      .build_call(function, args.as_slice(), "call")
      .map_err(|e| e.to_string())?
      .try_as_basic_value()
      .left()
      .ok_or(format!("Function {} does not return a value", name))?;

    Ok(result)
  }

  fn compile_display(
    &mut self,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>, String> {
    if args.len() != 1 {
      return Err("Display requires exactly 1 argument".to_string());
    }

    let value = self.compile_expression(&args[0])?;

    let printf = self
      .module
      .get_function("printf")
      .ok_or("Printf function not found".to_string())?;

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
      _ => return Err("Unsupported type for display".to_string()),
    };

    self
      .builder
      .build_call(
        printf,
        &[format_string.as_pointer_value().into(), value.into()],
        "printf_call",
      )
      .map_err(|e| e.to_string())?
      .try_as_basic_value()
      .left()
      .ok_or("Printf should return a value".to_string())?;

    Ok(value)
  }

  fn compile_begin(
    &mut self,
    args: &[Expression],
  ) -> Result<BasicValueEnum<'ctx>, String> {
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

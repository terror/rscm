use {
  crate::ast::{Atom, Expression},
  inkwell::{
    AddressSpace,
    builder::Builder,
    context::Context,
    module::Module,
    values::{BasicValueEnum, FunctionValue, PointerValue},
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
    let i32_type = self.context.i32_type();

    let fn_type = i32_type.fn_type(&[], false);

    let function = self.module.add_function("main", fn_type, None);

    let basic_block = self.context.append_basic_block(function, "entry");

    self.builder.position_at_end(basic_block);

    self.current_function = Some(function);

    self.declare_stdlib_functions();
    self.initialize_global_env();

    let mut result = None;

    for expr in expressions {
      result = Some(self.compile_expression(expr)?);
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
    // Create global variables for primitive operations
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
      _ => todo!(),
    }
  }

  fn compile_atom(&self, atom: &Atom) -> Result<BasicValueEnum<'ctx>, String> {
    match atom {
      Atom::Boolean(b) => {
        let val = self.context.bool_type().const_int(*b as u64, false);
        Ok(val.into())
      }
      Atom::Number(_) => todo!(),
      Atom::String(s) => {
        let string_const = self
          .builder
          .build_global_string_ptr(s, "string_const")
          .map_err(|e| e.to_string())?;

        Ok(string_const.as_pointer_value().into())
      }
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

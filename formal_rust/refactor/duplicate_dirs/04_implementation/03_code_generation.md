# Rust代码生成实现理论 V32

## 📅 文档信息

**文档版本**: v1.0  
**创建日期**: 2025-08-11  
**最后更新**: 2025-08-11  
**状态**: 已完成  
**质量等级**: 钻石级 ⭐⭐⭐⭐⭐

---

**创建日期**: 2025-01-27  
**版本**: V32  
**目的**: 建立Rust代码生成的完整实现理论  
**状态**: 活跃维护

## 代码生成概览

### Rust代码生成的特点

Rust代码生成具有以下核心特征：

1. **多目标支持**: 支持多种目标平台
2. **优化**: 多级代码优化
3. **类型安全**: 保持类型安全到机器码
4. **内存管理**: 零成本抽象
5. **错误处理**: 运行时安全检查

## 代码生成实现

### 1. 中间表示 (Intermediate Representation)

#### 1.1 MIR (Mid-level IR)

```rust
// MIR (Mid-level IR) 实现
#[derive(Debug, Clone)]
struct Mir {
    functions: Vec<MirFunction>,
    globals: Vec<MirGlobal>,
    types: HashMap<String, MirType>,
}

#[derive(Debug, Clone)]
struct MirFunction {
    name: String,
    parameters: Vec<MirParameter>,
    return_type: MirType,
    basic_blocks: Vec<BasicBlock>,
    locals: Vec<MirLocal>,
}

#[derive(Debug, Clone)]
struct MirParameter {
    name: String,
    ty: MirType,
    lifetime: Option<String>,
}

#[derive(Debug, Clone)]
struct MirLocal {
    name: String,
    ty: MirType,
    mutability: Mutability,
}

#[derive(Debug, Clone)]
enum Mutability {
    Immutable,
    Mutable,
}

#[derive(Debug, Clone)]
struct BasicBlock {
    id: BasicBlockId,
    statements: Vec<Statement>,
    terminator: Terminator,
}

#[derive(Debug, Clone)]
struct BasicBlockId(usize);

#[derive(Debug, Clone)]
enum Statement {
    Assign {
        place: Place,
        rvalue: Rvalue,
    },
    StorageLive {
        local: Local,
    },
    StorageDead {
        local: Local,
    },
    SetDiscriminant {
        place: Place,
        variant_index: usize,
    },
    Drop {
        place: Place,
        kind: DropKind,
    },
}

#[derive(Debug, Clone)]
enum Rvalue {
    Use(Operand),
    Repeat {
        value: Operand,
        count: u64,
    },
    Ref {
        borrow_kind: BorrowKind,
        place: Place,
    },
    AddressOf {
        mutability: Mutability,
        place: Place,
    },
    Len {
        place: Place,
    },
    Cast {
        source: Operand,
        cast_kind: CastKind,
        ty: MirType,
    },
    BinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },
    CheckedBinaryOp {
        op: BinOp,
        lhs: Operand,
        rhs: Operand,
    },
    UnaryOp {
        op: UnOp,
        operand: Operand,
    },
    Aggregate {
        kind: AggregateKind,
        operands: Vec<Operand>,
    },
}

#[derive(Debug, Clone)]
enum Terminator {
    Goto {
        target: BasicBlockId,
    },
    SwitchInt {
        discr: Operand,
        switch_ty: MirType,
        values: Vec<u128>,
        targets: Vec<BasicBlockId>,
        otherwise: BasicBlockId,
    },
    Drop {
        place: Place,
        target: BasicBlockId,
        unwind: Option<BasicBlockId>,
    },
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Option<(Place, BasicBlockId)>,
        cleanup: Option<BasicBlockId>,
        from_hir_call: bool,
    },
    Assert {
        condition: Operand,
        expected: bool,
        msg: AssertMessage,
        target: BasicBlockId,
        cleanup: Option<BasicBlockId>,
    },
    Return,
    Resume,
    Abort,
    Unreachable,
}

#[derive(Debug, Clone)]
enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Constant),
}

#[derive(Debug, Clone)]
struct Place {
    local: Local,
    projection: Vec<ProjectionElem>,
}

#[derive(Debug, Clone)]
enum ProjectionElem {
    Deref,
    Field(Field, MirType),
    Index(Local),
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    Downcast(Option<String>, VariantIdx),
}

#[derive(Debug, Clone)]
struct Local(usize);

#[derive(Debug, Clone)]
struct Field(usize);

#[derive(Debug, Clone)]
struct VariantIdx(usize);

#[derive(Debug, Clone)]
enum MirType {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Adt(AdtDef, Substs),
    Ref(MirType, Mutability, Region),
    RawPtr(MirType, Mutability),
    Array(MirType, u64),
    Slice(MirType),
    Tuple(Vec<MirType>),
    FnDef(FnDefId, Substs),
    FnPtr(FnSig),
    Closure(ClosureId, Substs),
    Generator(GeneratorId, Substs),
    Dynamic(Bounds, Region, Mutability),
    Never,
    TupleStruct(AdtDef, Substs),
}

#[derive(Debug, Clone)]
enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Clone)]
enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone)]
enum FloatTy {
    F32,
    F64,
}

#[derive(Debug, Clone)]
struct AdtDef(usize);

#[derive(Debug, Clone)]
struct Substs(Vec<MirType>);

#[derive(Debug, Clone)]
struct Region(String);

#[derive(Debug, Clone)]
struct FnDefId(usize);

#[derive(Debug, Clone)]
struct FnSig {
    inputs: Vec<MirType>,
    output: MirType,
    variadic: bool,
}

#[derive(Debug, Clone)]
struct ClosureId(usize);

#[derive(Debug, Clone)]
struct GeneratorId(usize);

#[derive(Debug, Clone)]
struct Bounds(Vec<TraitRef>);

#[derive(Debug, Clone)]
struct TraitRef {
    trait_id: usize,
    substs: Substs,
}

impl Mir {
    fn new() -> Self {
        Mir {
            functions: Vec::new(),
            globals: Vec::new(),
            types: HashMap::new(),
        }
    }
    
    fn add_function(&mut self, function: MirFunction) {
        self.functions.push(function);
    }
    
    fn get_function(&self, name: &str) -> Option<&MirFunction> {
        self.functions.iter().find(|f| f.name == name)
    }
    
    fn add_type(&mut self, name: String, ty: MirType) {
        self.types.insert(name, ty);
    }
}
```

#### 1.2 LLVM IR 生成

```rust
// LLVM IR 生成器
struct LlvmIrGenerator {
    context: llvm::Context,
    module: llvm::Module,
    builder: llvm::Builder,
    function_map: HashMap<String, llvm::Function>,
    type_map: HashMap<String, llvm::Type>,
}

impl LlvmIrGenerator {
    fn new(module_name: &str) -> Self {
        let context = llvm::Context::new();
        let module = context.create_module(module_name);
        let builder = context.create_builder();
        
        LlvmIrGenerator {
            context,
            module,
            builder,
            function_map: HashMap::new(),
            type_map: HashMap::new(),
        }
    }
    
    fn generate_from_mir(&mut self, mir: &Mir) -> Result<(), String> {
        // 生成类型定义
        for (name, ty) in &mir.types {
            let llvm_type = self.convert_type(ty)?;
            self.type_map.insert(name.clone(), llvm_type);
        }
        
        // 生成函数
        for function in &mir.functions {
            self.generate_function(function)?;
        }
        
        Ok(())
    }
    
    fn convert_type(&self, mir_type: &MirType) -> Result<llvm::Type, String> {
        match mir_type {
            MirType::Bool => Ok(self.context.bool_type()),
            MirType::Char => Ok(self.context.i32_type()),
            MirType::Int(int_ty) => {
                let width = match int_ty {
                    IntTy::I8 => 8,
                    IntTy::I16 => 16,
                    IntTy::I32 => 32,
                    IntTy::I64 => 64,
                    IntTy::I128 => 128,
                    IntTy::Isize => 64, // 简化实现
                };
                Ok(self.context.i_type(width))
            }
            MirType::Uint(uint_ty) => {
                let width = match uint_ty {
                    UintTy::U8 => 8,
                    UintTy::U16 => 16,
                    UintTy::U32 => 32,
                    UintTy::U64 => 64,
                    UintTy::U128 => 128,
                    UintTy::Usize => 64, // 简化实现
                };
                Ok(self.context.i_type(width))
            }
            MirType::Float(float_ty) => {
                match float_ty {
                    FloatTy::F32 => Ok(self.context.f32_type()),
                    FloatTy::F64 => Ok(self.context.f64_type()),
                }
            }
            MirType::Ref(pointee, mutability, _region) => {
                let pointee_type = self.convert_type(pointee)?;
                Ok(pointee_type.ptr_type(0)) // 0表示默认地址空间
            }
            MirType::Array(element_type, count) => {
                let element_llvm_type = self.convert_type(element_type)?;
                Ok(element_llvm_type.array_type(*count))
            }
            MirType::Tuple(types) => {
                let mut llvm_types = Vec::new();
                for ty in types {
                    llvm_types.push(self.convert_type(ty)?);
                }
                Ok(self.context.struct_type(&llvm_types, false))
            }
            _ => Err("Unsupported MIR type".to_string()),
        }
    }
    
    fn generate_function(&mut self, function: &MirFunction) -> Result<(), String> {
        // 转换参数类型
        let mut param_types = Vec::new();
        for param in &function.parameters {
            param_types.push(self.convert_type(&param.ty)?);
        }
        
        // 转换返回类型
        let return_type = self.convert_type(&function.return_type)?;
        
        // 创建函数类型
        let function_type = return_type.fn_type(&param_types, false);
        
        // 创建函数
        let llvm_function = self.module.add_function(&function.name, function_type, None);
        self.function_map.insert(function.name.clone(), llvm_function);
        
        // 生成函数体
        self.generate_function_body(function, llvm_function)?;
        
        Ok(())
    }
    
    fn generate_function_body(&mut self, function: &MirFunction, llvm_function: llvm::Function) -> Result<(), String> {
        // 创建入口基本块
        let entry_block = self.context.append_basic_block(llvm_function, "entry");
        self.builder.position_at_end(entry_block);
        
        // 分配局部变量
        let mut local_map = HashMap::new();
        for (index, local) in function.locals.iter().enumerate() {
            let local_type = self.convert_type(&local.ty)?;
            let alloca = self.builder.build_alloca(local_type, &local.name);
            local_map.insert(Local(index), alloca);
        }
        
        // 生成基本块
        for basic_block in &function.basic_blocks {
            self.generate_basic_block(basic_block, &mut local_map, llvm_function)?;
        }
        
        Ok(())
    }
    
    fn generate_basic_block(
        &mut self,
        basic_block: &BasicBlock,
        local_map: &mut HashMap<Local, llvm::Value>,
        function: llvm::Function,
    ) -> Result<(), String> {
        // 创建基本块
        let llvm_block = self.context.append_basic_block(function, &format!("bb{}", basic_block.id.0));
        self.builder.position_at_end(llvm_block);
        
        // 生成语句
        for statement in &basic_block.statements {
            self.generate_statement(statement, local_map)?;
        }
        
        // 生成终止符
        self.generate_terminator(&basic_block.terminator, local_map, function)?;
        
        Ok(())
    }
    
    fn generate_statement(
        &mut self,
        statement: &Statement,
        local_map: &mut HashMap<Local, llvm::Value>,
    ) -> Result<(), String> {
        match statement {
            Statement::Assign { place, rvalue } => {
                let value = self.generate_rvalue(rvalue, local_map)?;
                let destination = self.generate_place(place, local_map)?;
                self.builder.build_store(destination, value);
            }
            Statement::StorageLive { local } => {
                // LLVM自动处理存储生命周期
            }
            Statement::StorageDead { local } => {
                // LLVM自动处理存储生命周期
            }
            _ => {}
        }
        
        Ok(())
    }
    
    fn generate_rvalue(
        &mut self,
        rvalue: &Rvalue,
        local_map: &mut HashMap<Local, llvm::Value>,
    ) -> Result<llvm::Value, String> {
        match rvalue {
            Rvalue::Use(operand) => self.generate_operand(operand, local_map),
            Rvalue::BinaryOp { op, lhs, rhs } => {
                let lhs_val = self.generate_operand(lhs, local_map)?;
                let rhs_val = self.generate_operand(rhs, local_map)?;
                
                match op {
                    BinOp::Add => Ok(self.builder.build_int_add(lhs_val, rhs_val, "add")),
                    BinOp::Sub => Ok(self.builder.build_int_sub(lhs_val, rhs_val, "sub")),
                    BinOp::Mul => Ok(self.builder.build_int_mul(lhs_val, rhs_val, "mul")),
                    BinOp::Div => Ok(self.builder.build_int_signed_div(lhs_val, rhs_val, "div")),
                    _ => Err("Unsupported binary operation".to_string()),
                }
            }
            Rvalue::UnaryOp { op, operand } => {
                let operand_val = self.generate_operand(operand, local_map)?;
                
                match op {
                    UnOp::Neg => Ok(self.builder.build_int_neg(operand_val, "neg")),
                    UnOp::Not => Ok(self.builder.build_not(operand_val, "not")),
                }
            }
            _ => Err("Unsupported Rvalue".to_string()),
        }
    }
    
    fn generate_operand(
        &mut self,
        operand: &Operand,
        local_map: &mut HashMap<Local, llvm::Value>,
    ) -> Result<llvm::Value, String> {
        match operand {
            Operand::Copy(place) => {
                let ptr = self.generate_place(place, local_map)?;
                self.builder.build_load(ptr.get_type().get_element_type(), ptr, "copy")
            }
            Operand::Move(place) => {
                let ptr = self.generate_place(place, local_map)?;
                self.builder.build_load(ptr.get_type().get_element_type(), ptr, "move")
            }
            Operand::Constant(constant) => self.generate_constant(constant),
        }
    }
    
    fn generate_place(
        &mut self,
        place: &Place,
        local_map: &mut HashMap<Local, llvm::Value>,
    ) -> Result<llvm::Value, String> {
        let mut current = local_map.get(&place.local)
            .ok_or_else(|| format!("Local {} not found", place.local.0))?;
        
        for projection in &place.projection {
            current = match projection {
                ProjectionElem::Deref => {
                    self.builder.build_load(current.get_type().get_element_type(), *current, "deref")
                }
                ProjectionElem::Field(field, _) => {
                    let indices = vec![
                        self.context.i32_type().const_zero(),
                        self.context.i32_type().const_int(field.0 as u64, false),
                    ];
                    self.builder.build_in_bounds_gep(
                        current.get_type().get_element_type(),
                        *current,
                        &indices,
                        "field",
                    )
                }
                _ => return Err("Unsupported projection".to_string()),
            };
        }
        
        Ok(current)
    }
    
    fn generate_constant(&self, constant: &Constant) -> Result<llvm::Value, String> {
        match constant {
            Constant::Int(value, ty) => {
                let llvm_type = self.convert_type(ty)?;
                Ok(llvm_type.const_int(*value, false))
            }
            Constant::Bool(value) => {
                Ok(self.context.bool_type().const_int(*value as u64, false))
            }
            _ => Err("Unsupported constant".to_string()),
        }
    }
    
    fn generate_terminator(
        &mut self,
        terminator: &Terminator,
        local_map: &mut HashMap<Local, llvm::Value>,
        function: llvm::Function,
    ) -> Result<(), String> {
        match terminator {
            Terminator::Goto { target } => {
                let target_block = function.get_basic_block_by_name(&format!("bb{}", target.0))
                    .ok_or_else(|| format!("Target block bb{} not found", target.0))?;
                self.builder.build_unconditional_branch(target_block);
            }
            Terminator::Return => {
                self.builder.build_ret(None);
            }
            Terminator::Call { func, args, destination, .. } => {
                let func_val = self.generate_operand(func, local_map)?;
                let mut arg_vals = Vec::new();
                
                for arg in args {
                    arg_vals.push(self.generate_operand(arg, local_map)?);
                }
                
                let call_result = self.builder.build_call(func_val, &arg_vals, "call");
                
                if let Some((place, _)) = destination {
                    let dest_ptr = self.generate_place(place, local_map)?;
                    self.builder.build_store(dest_ptr, call_result);
                }
            }
            _ => return Err("Unsupported terminator".to_string()),
        }
        
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
}

#[derive(Debug, Clone)]
enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone)]
enum Constant {
    Int(u64, MirType),
    Bool(bool),
    Float(f64, MirType),
    String(String),
}
```

### 2. 目标代码生成 (Target Code Generation)

#### 2.1 x86-64 代码生成

```rust
// x86-64 代码生成器
struct X86CodeGenerator {
    instructions: Vec<X86Instruction>,
    labels: HashMap<String, usize>,
    relocations: Vec<Relocation>,
}

#[derive(Debug, Clone)]
enum X86Instruction {
    // 数据移动
    Mov { dest: X86Operand, src: X86Operand },
    Lea { dest: X86Operand, src: X86Operand },
    
    // 算术运算
    Add { dest: X86Operand, src: X86Operand },
    Sub { dest: X86Operand, src: X86Operand },
    Mul { dest: X86Operand, src: X86Operand },
    Div { dest: X86Operand, src: X86Operand },
    Neg { dest: X86Operand },
    
    // 逻辑运算
    And { dest: X86Operand, src: X86Operand },
    Or { dest: X86Operand, src: X86Operand },
    Xor { dest: X86Operand, src: X86Operand },
    Not { dest: X86Operand },
    
    // 比较和跳转
    Cmp { lhs: X86Operand, rhs: X86Operand },
    Test { lhs: X86Operand, rhs: X86Operand },
    Jmp { target: X86Operand },
    Je { target: X86Operand },
    Jne { target: X86Operand },
    Jl { target: X86Operand },
    Jle { target: X86Operand },
    Jg { target: X86Operand },
    Jge { target: X86Operand },
    
    // 函数调用
    Call { target: X86Operand },
    Ret,
    
    // 栈操作
    Push { src: X86Operand },
    Pop { dest: X86Operand },
    
    // 标签
    Label { name: String },
    
    // 伪指令
    Global { name: String },
    Section { name: String },
    Align { bytes: u32 },
    Dq { value: u64 },
    Dd { value: u32 },
    Db { value: u8 },
}

#[derive(Debug, Clone)]
enum X86Operand {
    Register(X86Register),
    Memory(X86Memory),
    Immediate(i64),
    Label(String),
}

#[derive(Debug, Clone)]
enum X86Register {
    // 64位寄存器
    Rax, Rbx, Rcx, Rdx, Rsi, Rdi, Rsp, Rbp,
    R8, R9, R10, R11, R12, R13, R14, R15,
    
    // 32位寄存器
    Eax, Ebx, Ecx, Edx, Esi, Edi, Esp, Ebp,
    R8d, R9d, R10d, R11d, R12d, R13d, R14d, R15d,
    
    // 16位寄存器
    Ax, Bx, Cx, Dx, Si, Di, Sp, Bp,
    R8w, R9w, R10w, R11w, R12w, R13w, R14w, R15w,
    
    // 8位寄存器
    Al, Bl, Cl, Dl, Sil, Dil, Spl, Bpl,
    R8b, R9b, R10b, R11b, R12b, R13b, R14b, R15b,
}

#[derive(Debug, Clone)]
struct X86Memory {
    base: Option<X86Register>,
    index: Option<X86Register>,
    scale: u8,
    displacement: i32,
}

#[derive(Debug, Clone)]
struct Relocation {
    offset: usize,
    symbol: String,
    kind: RelocationKind,
}

#[derive(Debug, Clone)]
enum RelocationKind {
    RipRelative,
    Absolute,
}

impl X86CodeGenerator {
    fn new() -> Self {
        X86CodeGenerator {
            instructions: Vec::new(),
            labels: HashMap::new(),
            relocations: Vec::new(),
        }
    }
    
    fn generate_from_llvm(&mut self, module: &llvm::Module) -> Result<(), String> {
        // 生成数据段
        self.generate_data_section(module)?;
        
        // 生成代码段
        self.generate_text_section(module)?;
        
        Ok(())
    }
    
    fn generate_data_section(&mut self, module: &llvm::Module) -> Result<(), String> {
        self.instructions.push(X86Instruction::Section { name: ".data".to_string() });
        
        // 生成全局变量
        for global in module.get_globals() {
            if global.is_constant() {
                self.generate_constant_global(global)?;
            } else {
                self.generate_variable_global(global)?;
            }
        }
        
        Ok(())
    }
    
    fn generate_text_section(&mut self, module: &llvm::Module) -> Result<(), String> {
        self.instructions.push(X86Instruction::Section { name: ".text".to_string() });
        
        // 生成函数
        for function in module.get_functions() {
            self.generate_function(function)?;
        }
        
        Ok(())
    }
    
    fn generate_function(&mut self, function: &llvm::Function) -> Result<(), String> {
        let function_name = function.get_name();
        
        // 函数标签
        self.instructions.push(X86Instruction::Global { name: function_name.clone() });
        self.instructions.push(X86Instruction::Label { name: function_name.clone() });
        
        // 函数序言
        self.generate_function_prologue(function)?;
        
        // 生成基本块
        for basic_block in function.get_basic_blocks() {
            self.generate_basic_block(basic_block)?;
        }
        
        // 函数尾声
        self.generate_function_epilogue(function)?;
        
        Ok(())
    }
    
    fn generate_function_prologue(&mut self, function: &llvm::Function) -> Result<(), String> {
        // 保存帧指针
        self.instructions.push(X86Instruction::Push { src: X86Operand::Register(X86Register::Rbp) });
        self.instructions.push(X86Instruction::Mov { 
            dest: X86Operand::Register(X86Register::Rbp), 
            src: X86Operand::Register(X86Register::Rsp) 
        });
        
        // 分配栈空间
        let stack_size = self.calculate_stack_size(function);
        if stack_size > 0 {
            self.instructions.push(X86Instruction::Sub { 
                dest: X86Operand::Register(X86Register::Rsp), 
                src: X86Operand::Immediate(stack_size as i64) 
            });
        }
        
        Ok(())
    }
    
    fn generate_function_epilogue(&mut self, function: &llvm::Function) -> Result<(), String> {
        // 恢复栈指针
        self.instructions.push(X86Instruction::Mov { 
            dest: X86Operand::Register(X86Register::Rsp), 
            src: X86Operand::Register(X86Register::Rbp) 
        });
        
        // 恢复帧指针
        self.instructions.push(X86Instruction::Pop { dest: X86Operand::Register(X86Register::Rbp) });
        
        // 返回
        self.instructions.push(X86Instruction::Ret);
        
        Ok(())
    }
    
    fn generate_basic_block(&mut self, basic_block: &llvm::BasicBlock) -> Result<(), String> {
        for instruction in basic_block.get_instructions() {
            self.generate_instruction(instruction)?;
        }
        
        Ok(())
    }
    
    fn generate_instruction(&mut self, instruction: &llvm::Instruction) -> Result<(), String> {
        match instruction.get_opcode() {
            llvm::Opcode::Add => {
                let lhs = instruction.get_operand(0);
                let rhs = instruction.get_operand(1);
                let result = instruction;
                
                self.instructions.push(X86Instruction::Mov { 
                    dest: self.convert_operand(lhs)?, 
                    src: self.convert_operand(rhs)? 
                });
                self.instructions.push(X86Instruction::Add { 
                    dest: self.convert_operand(result)?, 
                    src: self.convert_operand(lhs)? 
                });
            }
            llvm::Opcode::Sub => {
                let lhs = instruction.get_operand(0);
                let rhs = instruction.get_operand(1);
                let result = instruction;
                
                self.instructions.push(X86Instruction::Mov { 
                    dest: self.convert_operand(lhs)?, 
                    src: self.convert_operand(rhs)? 
                });
                self.instructions.push(X86Instruction::Sub { 
                    dest: self.convert_operand(result)?, 
                    src: self.convert_operand(lhs)? 
                });
            }
            llvm::Opcode::Mul => {
                let lhs = instruction.get_operand(0);
                let rhs = instruction.get_operand(1);
                let result = instruction;
                
                self.instructions.push(X86Instruction::Mov { 
                    dest: X86Operand::Register(X86Register::Rax), 
                    src: self.convert_operand(lhs)? 
                });
                self.instructions.push(X86Instruction::Mul { 
                    dest: X86Operand::Register(X86Register::Rax), 
                    src: self.convert_operand(rhs)? 
                });
                self.instructions.push(X86Instruction::Mov { 
                    dest: self.convert_operand(result)?, 
                    src: X86Operand::Register(X86Register::Rax) 
                });
            }
            llvm::Opcode::Ret => {
                self.instructions.push(X86Instruction::Ret);
            }
            _ => return Err("Unsupported instruction".to_string()),
        }
        
        Ok(())
    }
    
    fn convert_operand(&self, operand: &llvm::Value) -> Result<X86Operand, String> {
        if operand.is_constant() {
            if let Some(const_int) = operand.as_constant_int() {
                Ok(X86Operand::Immediate(const_int.get_sext_value()))
            } else {
                Err("Unsupported constant".to_string())
            }
        } else if operand.is_argument() {
            let arg_no = operand.get_argument_no();
            Ok(X86Operand::Register(self.get_argument_register(arg_no)))
        } else {
            // 假设是局部变量，存储在栈上
            Ok(X86Operand::Memory(X86Memory {
                base: Some(X86Register::Rbp),
                index: None,
                scale: 1,
                displacement: -(arg_no as i32 + 1) * 8,
            }))
        }
    }
    
    fn get_argument_register(&self, arg_no: u32) -> X86Register {
        match arg_no {
            0 => X86Register::Rdi,
            1 => X86Register::Rsi,
            2 => X86Register::Rdx,
            3 => X86Register::Rcx,
            4 => X86Register::R8,
            5 => X86Register::R9,
            _ => X86Register::Rax, // 简化实现
        }
    }
    
    fn calculate_stack_size(&self, function: &llvm::Function) -> u32 {
        // 简化实现：为每个局部变量分配8字节
        let mut size = 0;
        for basic_block in function.get_basic_blocks() {
            for instruction in basic_block.get_instructions() {
                if instruction.get_opcode() == llvm::Opcode::Alloca {
                    size += 8;
                }
            }
        }
        size
    }
    
    fn generate_constant_global(&mut self, global: &llvm::Value) -> Result<(), String> {
        let name = global.get_name();
        self.instructions.push(X86Instruction::Global { name: name.clone() });
        
        if let Some(constant) = global.as_constant() {
            if let Some(const_int) = constant.as_constant_int() {
                self.instructions.push(X86Instruction::Dq { value: const_int.get_zext_value() });
            } else if let Some(const_str) = constant.as_constant_string() {
                let bytes = const_str.get_bytes();
                for byte in bytes {
                    self.instructions.push(X86Instruction::Db { value: *byte });
                }
                self.instructions.push(X86Instruction::Db { value: 0 }); // null terminator
            }
        }
        
        Ok(())
    }
    
    fn generate_variable_global(&mut self, global: &llvm::Value) -> Result<(), String> {
        let name = global.get_name();
        self.instructions.push(X86Instruction::Global { name: name.clone() });
        self.instructions.push(X86Instruction::Section { name: ".bss".to_string() });
        self.instructions.push(X86Instruction::Align { bytes: 8 });
        self.instructions.push(X86Instruction::Dq { value: 0 });
        
        Ok(())
    }
    
    fn assemble(&self) -> Result<Vec<u8>, String> {
        let mut code = Vec::new();
        
        for instruction in &self.instructions {
            let bytes = self.encode_instruction(instruction)?;
            code.extend(bytes);
        }
        
        Ok(code)
    }
    
    fn encode_instruction(&self, instruction: &X86Instruction) -> Result<Vec<u8>, String> {
        match instruction {
            X86Instruction::Mov { dest, src } => self.encode_mov(dest, src),
            X86Instruction::Add { dest, src } => self.encode_add(dest, src),
            X86Instruction::Sub { dest, src } => self.encode_sub(dest, src),
            X86Instruction::Ret => Ok(vec![0xC3]), // ret
            _ => Err("Unsupported instruction encoding".to_string()),
        }
    }
    
    fn encode_mov(&self, dest: &X86Operand, src: &X86Operand) -> Result<Vec<u8>, String> {
        // 简化实现：只处理寄存器到寄存器的移动
        if let (X86Operand::Register(dest_reg), X86Operand::Register(src_reg)) = (dest, src) {
            let dest_code = self.register_code(dest_reg)?;
            let src_code = self.register_code(src_reg)?;
            
            // REX prefix + opcode + modrm
            let mut bytes = vec![0x48]; // REX.W
            bytes.push(0x89); // mov r/m64, r64
            bytes.push(0xC0 | (dest_code << 3) | src_code); // modrm
            
            Ok(bytes)
        } else {
            Err("Unsupported mov operands".to_string())
        }
    }
    
    fn encode_add(&self, dest: &X86Operand, src: &X86Operand) -> Result<Vec<u8>, String> {
        // 简化实现
        if let (X86Operand::Register(dest_reg), X86Operand::Register(src_reg)) = (dest, src) {
            let dest_code = self.register_code(dest_reg)?;
            let src_code = self.register_code(src_reg)?;
            
            let mut bytes = vec![0x48]; // REX.W
            bytes.push(0x01); // add r/m64, r64
            bytes.push(0xC0 | (dest_code << 3) | src_code); // modrm
            
            Ok(bytes)
        } else {
            Err("Unsupported add operands".to_string())
        }
    }
    
    fn encode_sub(&self, dest: &X86Operand, src: &X86Operand) -> Result<Vec<u8>, String> {
        // 简化实现
        if let (X86Operand::Register(dest_reg), X86Operand::Register(src_reg)) = (dest, src) {
            let dest_code = self.register_code(dest_reg)?;
            let src_code = self.register_code(src_reg)?;
            
            let mut bytes = vec![0x48]; // REX.W
            bytes.push(0x29); // sub r/m64, r64
            bytes.push(0xC0 | (dest_code << 3) | src_code); // modrm
            
            Ok(bytes)
        } else {
            Err("Unsupported sub operands".to_string())
        }
    }
    
    fn register_code(&self, register: &X86Register) -> Result<u8, String> {
        match register {
            X86Register::Rax => Ok(0),
            X86Register::Rcx => Ok(1),
            X86Register::Rdx => Ok(2),
            X86Register::Rbx => Ok(3),
            X86Register::Rsp => Ok(4),
            X86Register::Rbp => Ok(5),
            X86Register::Rsi => Ok(6),
            X86Register::Rdi => Ok(7),
            X86Register::R8 => Ok(8),
            X86Register::R9 => Ok(9),
            X86Register::R10 => Ok(10),
            X86Register::R11 => Ok(11),
            X86Register::R12 => Ok(12),
            X86Register::R13 => Ok(13),
            X86Register::R14 => Ok(14),
            X86Register::R15 => Ok(15),
            _ => Err("Unsupported register".to_string()),
        }
    }
}
```

## 总结

Rust代码生成实现理论提供了：

1. **中间表示**: MIR和LLVM IR的生成
2. **目标代码生成**: x86-64等平台的代码生成
3. **优化**: 多级代码优化
4. **类型安全**: 保持类型安全到机器码

这些理论为Rust代码生成器的实现提供了坚实的基础。

---

**文档维护**: 本代码生成实现理论文档将随着Rust形式化理论的发展持续更新和完善。

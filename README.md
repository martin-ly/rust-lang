
# rust-lang

## rust programming language learning - pre-knowledge

[rust-cpp-lang](docs/rust_cpp.md)
[rust-lang-model](docs/ownership_borrow_lifetime.md)
[rust-borrow-checker](docs/borrow_check.md)

### 1. Programming language model: include { variable, type system, control_flow }

    1.1 reference relative relationship lifetime syntax model: include { variable } 
    1.2 resource defination and organization,lifecycle RAII model: include { type system }
    1.3 runtime behavior Semantic model: include { control_flow }

[memory](docs/memory.md)

### 2. variable syntax model: include { own, borrow, scope }

    2.1 Ownership concept for human inference,Compiler Syntax Semantic check: include { Copy Semantic, Clone Semantic, Move Semantic }, 
    2.2 Defination,Modify explict Semantic: include { let,constant, ref, mut, ref mut }
    2.3 Copy implicit Semantic on Primitive Types: include{ number, boolean,etc internal Types}
    2.4 Clone explicit Semantic on Types
    2.5 Move implicit Semantic on Compound or Composite Types(programmer define types): include{ struct, enum, tuple, array, etc},
    2.6 Static check on move Semantic in Compiling time,variable's validate,Ownership's linear moving: include { visibility, shadow, scope ,only one owner},
    2.7 Runtime check on move Semantic in Compiling time or runtime,
    2.8 Scope and visibility semantic model: include { global, local, static,function,closure,expression }

[variable](docs/variable.md)
[ref_mut_reason](docs/ref_mut_reason.md)

### 3. type system model: include { primitive_type, compound_type, generic_type, trait_type }

    3.1 primitive_type: include{ number, boolean,etc internal Types}
    3.2 compound_type: include{  tuple, array, slice, string,etc}
    3.3 composite_type: include{ struct, enum }
    3.4 type_of_type: include{ type_alias, type_newtype, impl, trait } 
    3.5 generic_type: include{ generic_function, generic_struct, generic_enum, generic_trait,generic_impl}
    3.6 async_type: include{ async_function, async_trait }
    3.7 type_transform: include{ type_cast: as, into, from,try_into, try_from }
    3.8 type_variance: include{ invariant_type, covariant_type, contravariance_type }

[variant](docs/variant.md)
[variant_reason](docs/variant_reason.md)
[invariant_type](docs/invariant_type.md)
[covariant_type](docs/covariant_type.md)
[contravariance_type](docs/contravariance_type.md)

### 4. control_flow model: include { function, closure, expression, statement }

    4.1 function: include{ function_define, function_call, function_signature }
    4.2 closure: include{ closure_define, closure_call }
    4.3 expression: include{ expression,match, expression_value }
    4.4 statement: include{ statement,if,else,while,for,label,loop,match,return,break,continue,yield,gen,async,await,macro }

### 5. package and engineer

[package_mod](docs/cargo_package_mod.md)

## 1. own_borrow_scope  

[ref_refmut](docs/ref_refmut.md)

## 2. type_system

## 3. control_fn

## 4. generic

## 5. threads

## 6. async

## 7. process

## 8. algorithms

[algorithms_01](docs/algorithms_01.md)
[algorithms_02](docs/algorithms_02.md)

## 9. design_pattern

[design_pattern_01](docs/design_pattern_01.md)
[design_pattern_02](docs/design_pattern_02.md)

## 10. networks

## 11. frameworks

## 12. middlewares

pub(crate) use clever_emu_primitives::bitfield;
pub(crate) use paste::paste;

macro_rules! opt_context {
    ($(#[$meta:meta])* $ty:ty => context $field:ident : $ctx_ty:ty) => {
        $(#[$meta])*
        impl $crate::decode::AsDecodeContext for $ty {
            type Context = $ctx_ty;

            fn as_context(&self) -> $ctx_ty {
                self.$field()
            }
        }
    };

    ($(#[$meta:meta])* $ty:ty) => {
        $(#[$meta])*
        impl $crate::decode::NoContext for $ty {}
    };
}

macro_rules! def_enum{
    {
        #[repr($base_ty:ident)]
        $(#[$outer_meta:meta])*
        $vis:vis enum $gname:ident @ $(#[$opcode_meta:meta])* $opcstart:literal .. $opcend:literal {
            $(#![$enum_meta:meta])*
            $($(#[$meta:meta])* $uop:ident {$($(#[$field_meta:meta])* $field_name:ident @ $range_begin:literal $(.. $range_end:literal)? : $ty:ty),* $(,)?} $(context $ctx_field:ident : $ctx_ty:ty)? = $uopc:literal),* $(,)?
        }
    } => {
        $crate::macros::paste!{
            $(#[$outer_meta])*
            $vis mod [<$gname:snake _bits>]{
                use super::*;
                $(::clever_emu_primitives::bitfield::bitfield!{
                    $(#[$meta])*
                    pub struct $uop : $base_ty{
                        $($(#[$field_meta])* $vis $field_name @ $range_begin $(.. $range_end)? : $ty),*
                    }
                }
                opt_context!($(#[$meta])* $uop $(=> context $ctx_field : $ctx_ty)?);
                )*
            }

            $crate::macros::bitfield!{
                $(#[$outer_meta])*
                $vis struct [<$gname Encoded>]: $base_ty{
                    $vis decodebits @ 0..$opcstart : $base_ty,
                    $(#[$opcode_meta])*
                    $vis discrim @ $opcstart .. $opcend : $base_ty,
                }
            }

            #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
            $(#[$outer_meta])*
            $(#[$enum_meta])*
            $vis enum $gname{
                $($(#[$meta])* $uop ([<$gname:snake _bits>]::$uop),)*

                #[doc(hidden)]
                __Invalid([<$gname Encoded>])
            }

            $(#[$outer_meta])*
            impl $gname{
                $vis fn encode(self) -> [<$gname Encoded>]{
                    match self{
                        $($(#[$meta])* Self:: $uop(payload) => [<$gname Encoded>]::with_discrim(<$base_ty>::new($uopc)).insert_decodebits(payload.bits()),)*
                        Self::__Invalid(payload) => payload,
                    }
                }

                $vis fn validate(self) -> bool{
                    match self{
                        $($(#[$meta])* Self:: $uop(payload) => payload.validate(),)*
                        Self::__Invalid(_) => false
                    }
                }

            }

            $(#[$outer_meta])*
            impl<R: ::clever_emu_primitives::bitfield::BitfieldTy> ::clever_emu_primitives::bitfield::FromBitfield<R> for $gname where [<$gname Encoded>]: ::clever_emu_primitives::bitfield::FromBitfield<R>{
                fn validate(self) -> bool{
                    self.validate()
                }

                fn from_bits(bits: R) -> Self{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::from_bits(bits).decode()
                }

                fn to_bits(self) -> R{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::to_bits(self.encode())
                }
            }


            $(#[$outer_meta])*
            impl ::clever_emu_primitives::bitfield::DisplayBitfield for $gname{
                fn present(&self) -> bool{
                    true
                }

                fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result{
                    f.write_str(name)?;
                    f.write_str(": ")?;
                    ::core::fmt::Display::fmt(self, f)
                }
            }

            $(#[$outer_meta])*
            impl ::core::fmt::Display for $gname{
                fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                    match self{
                        $($(#[$meta])* Self:: $uop (payload) => {
                            f.write_str(::core::stringify!($uop))?;
                            payload.fmt(f)
                        },)*
                        Self::__Invalid(payload) => {
                            f.write_fmt(format_args!("**invalid {}: {:#x}**", ::core::stringify!([<$gname:snake>]), payload.bits()))
                        }
                    }
                }
            }


            $(#[$outer_meta])*
            impl [<$gname Encoded>]{
                $vis fn decode(self) -> $gname{
                    match self.discrim().get(){
                        $($(#[$meta])* $uopc => $gname :: $uop ( [<$gname:snake _bits>]::$uop::from_bits(self.decodebits())),)*
                        __inval => $gname::__Invalid(self)
                    }
                }
            }
        }
    }
}

macro_rules! capturing_enum{
    {
        #[repr($base_ty:ident)]
        $(#[$outer_meta:meta])*
        $vis:vis enum $gname:ident @ $(#[$opcode_meta:meta])* $opcstart:literal .. $opcend:literal {
            $(#![$enum_meta:meta])*
            $($uop:ident ($field:ty) = $uopc:literal,)*
            #[default] $last_uop:ident ($last_field:ty)
            $(,)?
        }
    } => {

        $crate::macros::paste!{
            $(#[$outer_meta])*
            $(#[$enum_meta])*
            #[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
            $vis enum $gname{
                $( $uop($field),)*
                $last_uop($last_field),
            }
            $crate::macros::bitfield!{
                $(#[$outer_meta])*
                $vis struct [<$gname Encoded>]: $base_ty{
                    $vis decodebits @ 0..$opcstart : $base_ty,
                    $(#[$opcode_meta])*
                    $vis discrim @ $opcstart .. $opcend : $base_ty,
                }
            }

            $(#[$outer_meta])*
            impl [<$gname Encoded>]{
                $vis fn decode(self) -> $gname{
                    match self.discrim().get(){
                        $( $uopc => $gname :: $uop(<$field>::from_bits(self.decodebits())),)*
                        _ => $gname:: $last_uop(<$last_field>::from_bits(self.bits()))
                    }
                }
            }

            $(#[$outer_meta])*
            impl $gname{
                $vis fn encode(self) -> [<$gname Encoded>]{
                    match self{
                        $(Self:: $uop(field) => [<$gname Encoded>]::with_discrim(<$base_ty>::new($uopc)).insert_decodebits(field.to_bits()),)*
                        Self:: $last_uop (last_field) => [<$gname Encoded>]::from_bits(last_field.to_bits())
                    }
                }

                $vis fn validate(self) -> bool {
                    match self{
                        $(Self:: $uop(payload) => payload.validate(),)*
                        Self::$last_uop(payload) => payload.validate(),
                    }
                }
            }

            $(#[$outer_meta])*
            impl<R: ::clever_emu_primitives::bitfield::BitfieldTy> ::clever_emu_primitives::bitfield::FromBitfield<R> for $gname where [<$gname Encoded>]: ::clever_emu_primitives::bitfield::FromBitfield<R>,
                $($field: ::clever_emu_primitives::bitfield::FromBitfield::<R>,)* $last_field: ::clever_emu_primitives::bitfield::FromBitfield::<R>{
                fn validate(self) -> bool{
                    self.validate()
                }

                fn from_bits(bits: R) -> Self{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::from_bits(bits).decode()
                }

                fn to_bits(self) -> R{
                    <[<$gname Encoded>] as ::clever_emu_primitives::bitfield::FromBitfield::<R>>::to_bits(self.encode())
                }
            }


            $(#[$outer_meta])*
            impl ::clever_emu_primitives::bitfield::DisplayBitfield for $gname{
                fn present(&self) -> bool{
                    true
                }

                fn display(&self, name: &str, f: &mut core::fmt::Formatter) -> core::fmt::Result{
                    f.write_str(name)?;
                    f.write_str(": ")?;
                    ::core::fmt::Display::fmt(self, f)
                }
            }

            $(#[$outer_meta])*
            impl ::core::fmt::Display for $gname{
                fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                    match self{
                        $(Self:: $uop (payload) => payload.fmt(f),)*
                        Self::$last_uop(payload) => payload.fmt(f)
                    }
                }
            }
        }
    }
}

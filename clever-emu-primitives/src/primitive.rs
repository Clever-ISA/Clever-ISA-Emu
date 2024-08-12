macro_rules! impl_le_integers_logic{
    {
        $(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident;)*
    } => {
        $(
            impl ::$($trait)::+ for $le_int_ty{
                type Output = Self;
                #[inline]
                fn $method(self, rhs: Self) -> Self{
                    Self(self.0.$method(rhs.0))
                }
            }

            impl ::$($trait)::+<&$le_int_ty> for $le_int_ty{
                type Output = Self;
                #[inline]
                fn $method(self, rhs: &Self) -> Self{
                    Self(self.0.$method(rhs.0))
                }
            }

            impl ::$($trait)::+<$le_int_ty> for &$le_int_ty{
                type Output = $le_int_ty;
                #[inline]
                fn $method(self, rhs: $le_int_ty) -> $le_int_ty{
                    $le_int_ty(self.0.$method(rhs.0))
                }
            }

            impl ::$($trait)::+<&$le_int_ty> for &$le_int_ty{
                type Output = $le_int_ty;
                #[inline]
                fn $method(self, rhs: &$le_int_ty) -> $le_int_ty{
                    $le_int_ty(self.0.$method(rhs.0))
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_arith{
    {
        $(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident;)*
    } => {
        $(
            impl ::$($trait)::+ for $le_int_ty{
                type Output = Self;

                #[inline]
                fn $method(self, rhs: Self) -> Self{
                    let this = self.get();
                    let rhs = rhs.get();
                    Self::new(this.$method(rhs))
                }
            }

            impl ::$($trait)::+ <&$le_int_ty> for $le_int_ty{
                type Output = Self;

                #[inline]
                fn $method(self, rhs: &Self) -> Self{
                    let this = self.get();
                    let rhs = rhs.get();
                    Self::new(this.$method(rhs))
                }
            }
            impl ::$($trait)::+ <$le_int_ty> for &$le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: $le_int_ty) -> $le_int_ty{
                    let this = self.get();
                    let rhs = rhs.get();
                    $le_int_ty::new(this.$method(rhs))
                }
            }

            impl ::$($trait)::+ for &$le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: Self) -> $le_int_ty{
                    let this = self.get();
                    let rhs = rhs.get();
                    $le_int_ty::new(this.$method(rhs))
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_shifts{
    {$(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident;)*} => {
        $(
            impl ::$($trait)::+ ::<u32> for $le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: u32) -> $le_int_ty{
                    $le_int_ty::new(self.get().$method(rhs))
                }
            }

            impl ::$($trait)::+ ::<u32> for &$le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: u32) -> $le_int_ty{
                    $le_int_ty::new((*self).get().$method(rhs))
                }
            }
        )*
    }
}

macro_rules! impl_le_integer_shift_assigns{
    {$(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident @ $op:tt;)*} => {
        $(impl ::$($trait)::+ ::<u32> for $le_int_ty{

            #[inline]
            fn $method(&mut self, rhs: u32){
                *self = *self $op rhs;
            }
        })*
    }
}

macro_rules! impl_le_integers_arith_base_ty{
    {
        $(impl ::$($trait:ident)::+ <$base_ty:ident> for $le_int_ty:ident = $method:ident;)*
    } => {
        $(
            impl ::$($trait)::+ <$base_ty> for $le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: $base_ty) -> $le_int_ty{
                    self.$method($le_int_ty::new(rhs))
                }
            }

            impl ::$($trait)::+ <&$base_ty> for $le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: &$base_ty) -> $le_int_ty{
                    self.$method($le_int_ty::new(*rhs))
                }
            }

            impl ::$($trait)::+ <$base_ty> for &$le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: $base_ty) -> $le_int_ty{
                    self.$method($le_int_ty::new(rhs))
                }
            }

            impl ::$($trait)::+ <&$base_ty> for &$le_int_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: &$base_ty) -> $le_int_ty{
                    self.$method($le_int_ty::new(*rhs))
                }
            }

            impl ::$($trait)::+ <$le_int_ty> for $base_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: $le_int_ty) -> $le_int_ty{
                    $le_int_ty::new(self).$method(rhs)
                }
            }

            impl ::$($trait)::+ <&$le_int_ty> for $base_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: &$le_int_ty) -> $le_int_ty{
                    $le_int_ty::new(self).$method(rhs)
                }
            }

            impl ::$($trait)::+ <$le_int_ty> for &$base_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: $le_int_ty) -> $le_int_ty{
                    $le_int_ty::new(*self).$method(rhs)
                }
            }
            impl ::$($trait)::+ <&$le_int_ty> for &$base_ty{
                type Output = $le_int_ty;

                #[inline]
                fn $method(self, rhs: &$le_int_ty) -> $le_int_ty{
                    $le_int_ty::new(*self).$method(rhs)
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_op_assign{
    {
        $(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident @ $op:tt;)*
    } => {
        $(
            impl ::$($trait)::+ for $le_int_ty{
                #[inline]
                fn $method(&mut self, rhs: Self){
                    *self = *self $op rhs;
                }
            }
            impl ::$($trait)::+ <&$le_int_ty> for $le_int_ty{
                #[inline]
                fn $method(&mut self, rhs: &Self){
                    *self = *self $op *rhs;
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_op_assign_base_ty{
    {
        $(impl ::$($trait:ident)::+<$base_ty:ident> for $le_int_ty:ident = $method:ident @ $op:tt;)*
    } => {
        $(
            impl ::$($trait)::+<$base_ty> for $le_int_ty{
                #[inline]
                fn $method(&mut self, rhs: $base_ty){
                    *self = *self $op rhs;
                }
            }
            impl ::$($trait)::+ <&$base_ty> for $le_int_ty{
                #[inline]
                fn $method(&mut self, rhs: &$base_ty){
                    *self = *self $op *rhs;
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_fmt{
    {
        $(impl ::$($trait:ident)::+ for $le_int_ty:ident;)*
    } => {
        $(
            impl ::$($trait)::+ for $le_int_ty{
                fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                    let this = self.get();

                    ::$($trait)::+ :: fmt(&this, f)
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_cmp_ref_only{
    {
        $(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident -> $ret_ty:ty;)*
    } => {
        $(

            impl ::$($trait)::+<&$le_int_ty> for $le_int_ty{
                fn $method(&self, rhs: &&$le_int_ty) -> $ret_ty{
                    let this = *self;

                    this.$method(*rhs)
                }
            }

            impl ::$($trait)::+<$le_int_ty> for &$le_int_ty{
                fn $method(&self, rhs: &$le_int_ty) -> $ret_ty{
                    let this = *self;

                    this.$method(rhs)
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_cmp{
    {
        $(impl ::$($trait:ident)::+ for $le_int_ty:ident = $method:ident -> $ret_ty:ty;)*
    } => {
        $(
            impl ::$($trait)::+<$le_int_ty> for $le_int_ty{
                fn $method(&self, rhs: &$le_int_ty) -> $ret_ty{
                    let this = self.get();
                    let rhs = rhs.get();

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<&$le_int_ty> for $le_int_ty{
                fn $method(&self, rhs: &&$le_int_ty) -> $ret_ty{
                    let this = self.get();
                    let rhs = rhs.get();

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<$le_int_ty> for &$le_int_ty{
                fn $method(&self, rhs: &$le_int_ty) -> $ret_ty{
                    let this = self.get();
                    let rhs = rhs.get();

                    this.$method(&rhs)
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_cmp_base_ty{
    {
        $(impl ::$($trait:ident)::+<$base_ty:ident> for $le_int_ty:ident = $method:ident -> $ret_ty:ty;)*
    } => {
        $(
            impl ::$($trait)::+<$base_ty> for $le_int_ty{
                fn $method(&self, rhs: &$base_ty) -> $ret_ty{
                    let this = self.get();
                    let rhs = *rhs;

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<&$base_ty> for $le_int_ty{
                fn $method(&self, rhs: &&$base_ty) -> $ret_ty{
                    let this = self.get();
                    let rhs = **rhs;

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<$base_ty> for &$le_int_ty{
                fn $method(&self, rhs: &$base_ty) -> $ret_ty{
                    let this = self.get();
                    let rhs = *rhs;

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<$le_int_ty> for $base_ty{
                fn $method(&self, rhs: &$le_int_ty) -> $ret_ty{
                    let this = *self;
                    let rhs = rhs.get();

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<&$le_int_ty> for $base_ty{
                fn $method(&self, rhs: &&$le_int_ty) -> $ret_ty{
                    let this = *self;
                    let rhs = rhs.get();

                    this.$method(&rhs)
                }
            }

            impl ::$($trait)::+<$le_int_ty> for &$base_ty{
                fn $method(&self, rhs: &$le_int_ty) -> $ret_ty{
                    let this = **self;
                    let rhs = rhs.get();

                    this.$method(&rhs)
                }
            }
        )*
    }
}

pub unsafe trait Truncate<T: bytemuck::Pod>: bytemuck::Pod {}
pub unsafe trait UnsignedAs<T: bytemuck::Pod>: bytemuck::Pod {
    const ZERO: T;
}

macro_rules! def_fix_endian_integers{
    {
        order $order:ident ($from_fixed_endian_name:ident: $to_fixed_endian_name:ident, $from_opposite_endian_name:ident: $to_opposite_endian_name:ident);
        $($vis:vis type $le_int_ty:ident = $base_ty:ident;)*
    } => {
        $(
            #[doc = concat!("A [`", stringify!($base_ty), "`] that is represented in memory as", stringify!($order), "-endian")]
            #[repr(transparent)]
            #[derive(Copy, Clone, Default, PartialEq, Eq, bytemuck::Zeroable, bytemuck::Pod)]
            $vis struct $le_int_ty($base_ty);

            impl $le_int_ty{

                pub const BITS: u32 = $base_ty::BITS;

                pub const MIN: Self = Self::new($base_ty::MIN);
                pub const MAX: Self = Self::new($base_ty::MAX);

                #[doc = concat!("Constructs an [`", stringify!($le_int_ty), "`] from it's base type. On big-endian platforms, this swaps the bytes of `x`")]
                $vis const fn new(x: $base_ty) -> Self{
                    Self::$from_fixed_endian_name(x.$to_fixed_endian_name())
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to it's base type. On big-endian platforms, this swaps the bytes of `x`")]
                $vis const fn get(self) -> $base_ty{
                    $base_ty::$from_fixed_endian_name(self.$to_fixed_endian_name())
                }


                #[doc = concat!("Constructs a [`", stringify!($le_int_ty), "`] from the raw LE bytes. This is zero cost on all platforms")]
                $vis const fn $from_fixed_endian_name(x: [u8;core::mem::size_of::<Self>()]) -> Self{
                    Self(<$base_ty>::from_ne_bytes(x))
                }

                #[doc = concat!("Constructs a [`", stringify!($le_int_ty), "`] from the raw BE bytes. This swaps bytes on all platforms")]
                $vis const fn $from_opposite_endian_name(x: [u8;core::mem::size_of::<Self>()]) -> Self{
                    Self(<$base_ty>::from_ne_bytes(x).swap_bytes())
                }

                #[doc = concat!("Constructs a [`", stringify!($le_int_ty), "`] from the raw bytes in native order. This swaps bytes on big-endian platforms\n",
                "This is equivalent to [`", stringify!($le_int_ty), "::new`] called with the result of [`", stringify!($base_ty),"::from_ne_bytes`]")]
                $vis const fn from_ne_bytes(x: [u8;core::mem::size_of::<Self>()]) -> Self{
                    Self::new(<$base_ty>::$from_fixed_endian_name(x))
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to the raw LE bytes. This is zero cost on all platforms")]
                $vis const fn $to_fixed_endian_name(self) -> [u8;core::mem::size_of::<Self>()]{
                    self.0.to_ne_bytes()
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to the raw BE bytes. This swaps bytes on all platforms")]
                $vis const fn $to_opposite_endian_name(self) -> [u8;core::mem::size_of::<Self>()]{
                    self.0.swap_bytes().to_ne_bytes()
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to the raw bytes in native order. This swaps bytes on big-endian platforms")]
                $vis const fn to_ne_bytes(self) -> [u8;core::mem::size_of::<Self>()]{
                    self.get().to_ne_bytes()
                }

                $vis const fn leading_zeros(self) -> u32{
                    self.get().leading_zeros()
                }

                $vis const fn trailing_zeros(self) -> u32{
                    self.get().trailing_zeros()
                }

                $vis const fn count_zeros(self) -> u32{
                    self.get().count_zeros()
                }

                $vis const fn leading_ones(self) -> u32{
                    self.get().leading_ones()
                }

                $vis const fn trailing_ones(self) -> u32{
                    self.get().trailing_ones()
                }

                $vis const fn count_ones(self) -> u32{
                    self.get().count_ones()
                }

                $vis const fn rotate_left(self, val: u32) -> Self{
                    Self::new(self.get().rotate_left(val))
                }
                $vis const fn rotate_right(self, val: u32) -> Self{
                    Self::new(self.get().rotate_right(val))
                }

                $vis const fn wrapping_add(self, val: $le_int_ty) -> Self{
                    Self::new(self.get().wrapping_add(val.get()))
                }

                $vis const fn wrapping_sub(self, val: $le_int_ty) -> Self{
                    Self::new(self.get().wrapping_sub(val.get()))
                }

                $vis const fn overflowing_sub(self, val: $le_int_ty) -> (Self, bool){
                    let (val, overflow) = self.get().overflowing_sub(val.get());

                    (Self::new(val), overflow)
                }

                $vis const fn overflowing_add(self, val: $le_int_ty) -> (Self, bool){
                    let (val, overflow) = self.get().overflowing_sub(val.get());

                    (Self::new(val), overflow)
                }

                $vis const fn wrapping_mul(self, val: $le_int_ty) -> Self{
                    Self::new(self.get().wrapping_mul(val.get()))
                }
            }

            impl ::core::convert::From<$base_ty> for $le_int_ty{
                fn from(x: $base_ty) -> Self{
                    Self::new(x)
                }
            }

            impl ::core::convert::From<$le_int_ty> for $base_ty{
                fn from(x: $le_int_ty) -> Self{
                    x.get()
                }
            }

            impl ::core::convert::From<&$base_ty> for $le_int_ty{
                fn from(x: &$base_ty) -> Self{
                    Self::new(*x)
                }
            }

            impl ::core::convert::From<&$le_int_ty> for $base_ty{
                fn from(x: &$le_int_ty) -> Self{
                    x.get()
                }
            }

            impl ::core::hash::Hash for $le_int_ty{
                fn hash<H: ::core::hash::Hasher>(&self, state: &mut H){
                    let val = self.get();
                    val.hash(state)
                }
            }

            impl ::core::cmp::Ord for $le_int_ty{
                #[inline]
                fn cmp(&self, other: &Self) -> ::core::cmp::Ordering{
                    let this = self.get();
                    let other = other.get();

                    this.cmp(&other)
                }
            }

            impl ::core::ops::Not for $le_int_ty{
                type Output = Self;
                #[inline]
                fn not(self) -> Self{
                    Self(!self.0)
                }
            }

            impl_le_integers_cmp_ref_only!{
                impl ::core::cmp::PartialEq for $le_int_ty = eq -> bool;
            }

            impl_le_integers_cmp!{
                impl ::core::cmp::PartialOrd for $le_int_ty = partial_cmp -> ::core::option::Option<::core::cmp::Ordering>;
            }
            impl_le_integers_cmp_base_ty!{
                impl ::core::cmp::PartialEq<$base_ty> for $le_int_ty = eq -> bool;
                impl ::core::cmp::PartialOrd<$base_ty> for $le_int_ty = partial_cmp -> ::core::option::Option<::core::cmp::Ordering>;
            }

            impl_le_integers_fmt!{
                impl ::core::fmt::Display for $le_int_ty;
                impl ::core::fmt::Debug for $le_int_ty;
                impl ::core::fmt::UpperHex for $le_int_ty;
                impl ::core::fmt::LowerHex for $le_int_ty;
                impl ::core::fmt::UpperExp for $le_int_ty;
                impl ::core::fmt::LowerExp for $le_int_ty;
                impl ::core::fmt::Octal for $le_int_ty;
                impl ::core::fmt::Binary for $le_int_ty;
            }

            impl_le_integers_logic!{
                impl ::core::ops::BitAnd for $le_int_ty = bitand;
                impl ::core::ops::BitOr for $le_int_ty = bitor;
                impl ::core::ops::BitXor for $le_int_ty = bitxor;
            }

            impl_le_integers_arith!{
                impl ::core::ops::Add for $le_int_ty = add;
                impl ::core::ops::Sub for $le_int_ty = sub;
                impl ::core::ops::Mul for $le_int_ty = mul;
                impl ::core::ops::Div for $le_int_ty = div;
                impl ::core::ops::Rem for $le_int_ty = rem;
                impl ::core::ops::Shr for $le_int_ty = shr;
                impl ::core::ops::Shl for $le_int_ty = shl;
            }

            impl_le_integers_arith_base_ty!{
                impl ::core::ops::Add<$base_ty> for $le_int_ty = add;
                impl ::core::ops::Sub<$base_ty> for $le_int_ty = sub;
                impl ::core::ops::Mul<$base_ty> for $le_int_ty = mul;
                impl ::core::ops::Div<$base_ty> for $le_int_ty = div;
                impl ::core::ops::Rem<$base_ty> for $le_int_ty = rem;
                impl ::core::ops::BitAnd<$base_ty> for $le_int_ty = bitand;
                impl ::core::ops::BitOr<$base_ty> for $le_int_ty = bitor;
                impl ::core::ops::BitXor<$base_ty> for $le_int_ty = bitxor;
            }

            impl_le_integers_op_assign!{
                impl ::core::ops::AddAssign for $le_int_ty = add_assign @ +;
                impl ::core::ops::SubAssign for $le_int_ty = sub_assign @ -;
                impl ::core::ops::BitAndAssign for $le_int_ty = bitand_assign @ &;
                impl ::core::ops::BitOrAssign for $le_int_ty = bitor_assign @ |;
                impl ::core::ops::BitXorAssign for $le_int_ty = bitxor_assign @ ^;
                impl ::core::ops::MulAssign for $le_int_ty = mul_assign @ *;
                impl ::core::ops::DivAssign for $le_int_ty = div_assign @ /;
                impl ::core::ops::RemAssign for $le_int_ty = rem_assign @ %;
                impl ::core::ops::ShrAssign for $le_int_ty = shr_assign @ >>;
                impl ::core::ops::ShlAssign for $le_int_ty = shl_assign @ <<;
            }

            impl_le_integers_op_assign_base_ty!{
                impl ::core::ops::AddAssign<$base_ty> for $le_int_ty = add_assign @ +;
                impl ::core::ops::SubAssign<$base_ty> for $le_int_ty = sub_assign @ -;
                impl ::core::ops::BitAndAssign<$base_ty> for $le_int_ty = bitand_assign @ &;
                impl ::core::ops::BitOrAssign<$base_ty> for $le_int_ty = bitor_assign @ |;
                impl ::core::ops::BitXorAssign<$base_ty> for $le_int_ty = bitxor_assign @ ^;
                impl ::core::ops::MulAssign<$base_ty> for $le_int_ty = mul_assign @ *;
                impl ::core::ops::DivAssign<$base_ty> for $le_int_ty = div_assign @ /;
                impl ::core::ops::RemAssign<$base_ty> for $le_int_ty = rem_assign @ %;
            }

            impl_le_integers_shifts!{
                impl ::core::ops::Shr for $le_int_ty = shr;
                impl ::core::ops::Shl for $le_int_ty = shl;
            }

            impl_le_integer_shift_assigns!{
                impl ::core::ops::ShrAssign for $le_int_ty = shr_assign @ >>;
                impl ::core::ops::ShlAssign for $le_int_ty = shl_assign @ <<;
            }
        )*
    }
}

macro_rules! impl_le_integers_neg{
    ($($le_int_ty:ident),*) => {
        $(impl ::core::ops::Neg for $le_int_ty{
            type Output = Self;
            #[inline]
            fn neg(self) -> Self{
                Self::new(-self.get())
            }
        })*
    }
}

macro_rules! impl_le_integers_cast_sign{
    {
        $($signed_ty:ident @ $unsigned_ty:ident;)*
    } => {
        $(
            impl $signed_ty{
                pub const fn cast_sign(self) -> $unsigned_ty{
                    $crate::const_transmute_safe(self)
                }
            }
            impl $unsigned_ty{
                pub const fn cast_sign(self) -> $signed_ty{
                    $crate::const_transmute_safe(self)
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_from{
    {$(impl From <$other_ty:ident> for $le_int_ty:ident;)*} => {
        $(
            impl ::core::convert::From<$other_ty> for $le_int_ty{
                fn from(x: $other_ty) -> Self{
                    Self::new(x.get().into())
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_unsigned_as_truncate{
    ($($le_int_ty:ident),*) => {
        $(
            impl $le_int_ty{
                pub const fn unsigned_as<T: bytemuck::Pod>(self) ->T where Self: UnsignedAs<T>{
                    union Transmuter<T>{
                        this: $le_int_ty,
                        other: core::mem::ManuallyDrop<T>
                    }

                    let mut transmuter = Transmuter{other: core::mem::ManuallyDrop::new(Self::ZERO)};
                    transmuter.this = self;


                    unsafe{core::mem::ManuallyDrop::into_inner(transmuter.other)}
                }
                pub const fn truncate_to<T>(self) -> T where T: Truncate<Self>{
                    union Transmuter<T>{
                        this: $le_int_ty,
                        other: core::mem::ManuallyDrop<T>
                    }

                    let transmuter = Transmuter{this: self};

                    unsafe{core::mem::ManuallyDrop::into_inner(transmuter.other)}
                }
            }
        )*
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TryFromIntError(());

impl core::fmt::Display for TryFromIntError {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        fmt.write_str("out of range integral type conversion attempted")
    }
}

impl std::error::Error for TryFromIntError {}

impl From<core::convert::Infallible> for TryFromIntError {
    fn from(x: core::convert::Infallible) -> TryFromIntError {
        match x {}
    }
}

macro_rules! impl_le_integers_tryfrom_signed{
    {
        $(impl TryFrom<$other_ty:ident> for $le_int_ty:ident;)*
    } => {
        $(
            impl ::core::convert::TryFrom<$other_ty> for $le_int_ty{
                type Error = TryFromIntError;

                fn try_from(x: $other_ty) -> Result<Self,Self::Error>{
                    let val = x.cast_sign();

                    if x < 0{
                        Err(TryFromIntError(()))
                    }else{
                        Ok(val.into())
                    }
                }
            }
        )*
    }
}

macro_rules! impl_le_integers_truncate{
    {
        $(unsafe impl Truncate <$other_ty:ident> for $le_int_ty:ident;)*
    } => {
        $(
            unsafe impl Truncate<$other_ty> for $le_int_ty{}

            impl ::core::convert::TryFrom<$other_ty> for $le_int_ty{
                type Error = TryFromIntError;

                fn try_from(x: $other_ty) -> Result<$le_int_ty,TryFromIntError>{
                    let trunc = x.truncate_to::<$le_int_ty>();


                    let newval = $other_ty::try_from(trunc)?;

                    if newval != x{
                        Err(TryFromIntError(()))
                    }else{
                        Ok(trunc)
                    }

                }
            }
        )*
    }
}

def_fix_endian_integers! {
    order little (from_le_bytes: to_le_bytes, from_be_bytes: to_be_bytes);
    pub type LeI8 = i8;
    pub type LeU8 = u8;
    pub type LeI16 = i16;
    pub type LeU16 = u16;
    pub type LeI32 = i32;
    pub type LeU32 = u32;
    pub type LeI64 = i64;
    pub type LeU64 = u64;
    pub type LeI128 = i128;
    pub type LeU128 = u128;
}

impl_le_integers_unsigned_as_truncate! {
    LeI8, LeU8, LeI16, LeU16, LeI32, LeU32, LeI64, LeU64, LeI128, LeU128
}

def_fix_endian_integers! {
    order big (from_le_bytes: to_le_bytes, from_be_bytes: to_be_bytes);
    pub type BeI8 = i8;
    pub type BeU8 = u8;
    pub type BeI16 = i16;
    pub type BeU16 = u16;
    pub type BeI32 = i32;
    pub type BeU32 = u32;
    pub type BeI64 = i64;
    pub type BeU64 = u64;
    pub type BeI128 = i128;
    pub type BeU128 = u128;
}

impl_le_integers_neg!(LeI8, LeI16, LeI32, LeI64, LeI128);

impl_le_integers_cast_sign! {
    LeI8 @ LeU8;
    LeI16 @ LeU16;
    LeI32 @ LeU32;
    LeI64 @ LeU64;
    LeI128 @ LeU128;
}

impl_le_integers_from! {
    impl From<LeI8>  for LeI16;
    impl From<LeI8>  for LeI32;
    impl From<LeI8>  for LeI64;
    impl From<LeI8>  for LeI128;
    impl From<LeI16> for LeI32;
    impl From<LeI16> for LeI64;
    impl From<LeI16> for LeI128;
    impl From<LeI32> for LeI64;
    impl From<LeI32> for LeI128;
    impl From<LeI64> for LeI128;

    impl From<LeU8>  for LeI16;
    impl From<LeU8>  for LeI32;
    impl From<LeU8>  for LeI64;
    impl From<LeU8>  for LeI128;
    impl From<LeU16> for LeI32;
    impl From<LeU16> for LeI64;
    impl From<LeU16> for LeI128;
    impl From<LeU32> for LeI64;
    impl From<LeU32> for LeI128;
    impl From<LeU64> for LeI128;

    impl From<LeU8>  for LeU16;
    impl From<LeU8>  for LeU32;
    impl From<LeU8>  for LeU64;
    impl From<LeU8>  for LeU128;
    impl From<LeU16> for LeU32;
    impl From<LeU16> for LeU64;
    impl From<LeU16> for LeU128;
    impl From<LeU32> for LeU64;
    impl From<LeU32> for LeU128;
    impl From<LeU64> for LeU128;
}

impl_le_integers_tryfrom_signed! {
    impl TryFrom<LeI8>  for LeU8;
    impl TryFrom<LeI8>  for LeU16;
    impl TryFrom<LeI8>  for LeU32;
    impl TryFrom<LeI8>  for LeU64;
    impl TryFrom<LeI8>  for LeU128;

    impl TryFrom<LeI16> for LeU16;
    impl TryFrom<LeI16> for LeU32;
    impl TryFrom<LeI16> for LeU64;
    impl TryFrom<LeI16> for LeU128;

    impl TryFrom<LeI32> for LeU32;
    impl TryFrom<LeI32> for LeU64;
    impl TryFrom<LeI32> for LeU128;

    impl TryFrom<LeI64> for LeU64;
    impl TryFrom<LeI64> for LeU128;

    impl TryFrom<LeI128> for LeU128;
}

impl_le_integers_truncate! {
    unsafe impl Truncate<LeU128> for LeU64;
    unsafe impl Truncate<LeU128> for LeU32;
    unsafe impl Truncate<LeU128> for LeU16;
    unsafe impl Truncate<LeU128> for LeU8 ;
    unsafe impl Truncate<LeU64>  for LeU32;
    unsafe impl Truncate<LeU64>  for LeU16;
    unsafe impl Truncate<LeU64>  for LeU8 ;
    unsafe impl Truncate<LeU32>  for LeU16;
    unsafe impl Truncate<LeU32>  for LeU8 ;
    unsafe impl Truncate<LeU16>  for LeU8 ;

    unsafe impl Truncate<LeU128> for LeI64;
    unsafe impl Truncate<LeU128> for LeI32;
    unsafe impl Truncate<LeU128> for LeI16;
    unsafe impl Truncate<LeU128> for LeI8 ;
    unsafe impl Truncate<LeU64>  for LeI32;
    unsafe impl Truncate<LeU64>  for LeI16;
    unsafe impl Truncate<LeU64>  for LeI8 ;
    unsafe impl Truncate<LeU32>  for LeI16;
    unsafe impl Truncate<LeU32>  for LeI8 ;
    unsafe impl Truncate<LeU16>  for LeI8 ;

    unsafe impl Truncate<LeI128> for LeI64;
    unsafe impl Truncate<LeI128> for LeI32;
    unsafe impl Truncate<LeI128> for LeI16;
    unsafe impl Truncate<LeI128> for LeI8 ;
    unsafe impl Truncate<LeI64>  for LeI32;
    unsafe impl Truncate<LeI64>  for LeI16;
    unsafe impl Truncate<LeI64>  for LeI8 ;
    unsafe impl Truncate<LeI32>  for LeI16;
    unsafe impl Truncate<LeI32>  for LeI8 ;
    unsafe impl Truncate<LeI16>  for LeI8 ;

    unsafe impl Truncate<LeI128> for LeU64;
    unsafe impl Truncate<LeI128> for LeU32;
    unsafe impl Truncate<LeI128> for LeU16;
    unsafe impl Truncate<LeI128> for LeU8 ;
    unsafe impl Truncate<LeI64>  for LeU32;
    unsafe impl Truncate<LeI64>  for LeU16;
    unsafe impl Truncate<LeI64>  for LeU8 ;
    unsafe impl Truncate<LeI32>  for LeU16;
    unsafe impl Truncate<LeI32>  for LeU8 ;
    unsafe impl Truncate<LeI16>  for LeU8 ;
}

macro_rules! impl_le_integers_unsigned_as{
    {
        $($base_ty:ident: $($as_tys:ident),*;)*
    } => {
        $(
            $(
                unsafe impl UnsignedAs<$as_tys> for $base_ty{
                    const ZERO: $as_tys = $as_tys::new(0);
                }
            )*
        )*
    }
}

impl_le_integers_unsigned_as! {
    LeU8: LeU8, LeU16, LeU32, LeU64, LeU128, LeI8, LeI16, LeI32, LeI64, LeI128;
    LeU16: LeU8, LeU16, LeU32, LeU64, LeU128, LeI8, LeI16, LeI32, LeI64, LeI128;
    LeU32: LeU8, LeU16, LeU32, LeU64, LeU128, LeI8, LeI16, LeI32, LeI64, LeI128;
    LeU64: LeU8, LeU16, LeU32, LeU64, LeU128, LeI8, LeI16, LeI32, LeI64, LeI128;
    LeU128: LeU8, LeU16, LeU32, LeU64, LeU128, LeI8, LeI16, LeI32, LeI64, LeI128;
    LeI8: LeU8, LeU16, LeU32, LeU64, LeU128;
    LeI16: LeU8, LeU16, LeU32, LeU64, LeU128;
    LeI32: LeU8, LeU16, LeU32, LeU64, LeU128;
    LeI64: LeU8, LeU16, LeU32, LeU64, LeU128;
    LeI128: LeU8, LeU16, LeU32, LeU64, LeU128;
}

#[macro_export]
macro_rules! le_fake_enum{
    {

        #[repr($field_vis:vis $repr:ident)]
        $(#[$meta:meta])*
        $vis:vis enum $name:ident{
            $( $(#[$meta2:meta])* $var:ident = $discrim:literal),*
            $(,)?
        }
    } => {

        #[repr(transparent)]
        #[derive(Copy, Clone, Hash, PartialEq, Eq)]
        $(#[$meta])*
        $vis struct $name($field_vis $crate::primitive::$repr);

        #[allow(non_upper_case_globals)]
        impl $name{
            $(
                $(#[$meta2:meta])* $vis const $var: Self = Self($crate::primitive::$repr::new($discrim));
            )*

            pub const fn validate(self) -> bool{
                match self.0.get(){
                    $($discrim => true,)*
                    _ => false
                }
            }
        }

        impl ::core::fmt::Display for $name{
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                match *self{
                    $(Self::$var => f.write_str(::core::stringify!($var)),)*
                    _ => {
                        f.write_str(::core::stringify!($name))?;
                        f.write_str("(")?;
                        self.0.fmt(f)?;
                        f.write_str(")")
                    }
                }
            }
        }

        impl ::core::fmt::Debug for $name{
            fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                match *self{
                    $(Self::$var => f.write_str(::core::stringify!($var)),)*
                    _ => {
                        f.write_str(::core::stringify!($name))?;
                        f.write_str("(")?;
                        self.0.fmt(f)?;
                        f.write_str(")")
                    }
                }
            }
        }

        impl<T: $crate::bitfield::BitfieldTy> $crate::bitfield::FromBitfield<T> for $name where $crate::primitive::$repr: $crate::bitfield::FromBitfield<T>{
            fn from_bits(bits: T) -> Self{
                Self($crate::bitfield::FromBitfield::<T>::from_bits(bits))
            }
            fn to_bits(self) -> T{
                $crate::bitfield::FromBitfield::<T>::to_bits(self.0)
            }

            fn validate(self) -> bool{
                self.validate()
            }
        }

        impl $crate::bitfield::DisplayBitfield for $name{
            fn present(&self) -> bool{
                true
            }
            fn display(&self, _: &str, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result{
                f.write_fmt(format_args!("{}",self))
            }
        }
    }
}

pub use le_fake_enum;

impl_le_integers_neg!(BeI8, BeI16, BeI32, BeI64, BeI128);

impl_le_integers_cast_sign! {
    BeI8 @ BeU8;
    BeI16 @ BeU16;
    BeI32 @ BeU32;
    BeI64 @ BeU64;
    BeI128 @ BeU128;
}

macro_rules! def_be_le_converts{
    {
        $($be_ty:ident => $le_ty:ident),*
        $(,)?
    } => {
        $(impl $be_ty{

            #[doc = concat!("Converts a [`", ::core::stringify!($le_ty),"`] to a [`",::core::stringify!($be_ty),"`]. This swaps bytes on all platforms")]
            pub const fn from_le(val: $le_ty) -> Self{
                Self(val.0.swap_bytes())
            }


            #[doc = concat!("Converts a [`", ::core::stringify!($be_ty),"`] to a [`",::core::stringify!($le_ty),"`]. This swaps bytes on all platforms")]
            pub const fn to_le(self) -> $le_ty{
                $le_ty(self.0.swap_bytes())
            }
        }

        impl $le_ty{

            #[doc = concat!("Converts a [`", ::core::stringify!($be_ty),"`] to a [`",::core::stringify!($le_ty),"`]. This swaps bytes on all platforms")]
            pub const fn from_be(val: $be_ty) -> Self{
                Self(val.0.swap_bytes())
            }

            #[doc = concat!("Converts a [`", ::core::stringify!($le_ty),"`] to a [`",::core::stringify!($be_ty),"`]. This swaps bytes on all platforms")]
            pub const fn to_be(self) -> $be_ty{
                $be_ty(self.0.swap_bytes())
            }
        })*
    }
}

def_be_le_converts! {
    BeI8 => LeI8,
    BeU8 => LeU8,
    BeI16 => LeI16,
    BeU16 => LeU16,
    BeI32 => LeI32,
    BeU32 => LeU32,
    BeI64 => LeI64,
    BeU64 => LeU64,
    BeI128 => LeI128,
    BeU128 => LeU128,
}

macro_rules! def_fixed_endian_widening_mul{
    ($($ty:ident ($width:literal)),* $(,)?) => {
        $(impl $ty{
            #[doc = concat!("Computes the complete product `self * other` without overflowing, returning the high order bits.")]
            #[doc = concat!("The result is (low, high) in that order, where the value of the product is `(high << ", ::core::stringify!($width), ") + low`, represented as an infinite range integer type")]
            pub const fn widening_mul(self, other: Self) -> (Self, Self){
                let (lo, hi) = self.get().widening_mul(other.get());

                (Self::new(lo), Self::new(hi))
            }
        })*
    }
}

def_fixed_endian_widening_mul!(LeU8(8), LeU16(16), LeU32(32), LeU64(64));

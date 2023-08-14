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

pub unsafe trait Truncate<T: bytemuck::Pod>: bytemuck::Pod {}

macro_rules! def_le_integers{
    {
        $($vis:vis type $le_int_ty:ident = $base_ty:ident;)*
    } => {
        $(
            #[doc = concat!("A [`", stringify!($base_ty), "`] that is represented in memory as little-endian")]
            #[repr(transparent)]
            #[derive(Copy, Clone, Default, bytemuck::Zeroable, bytemuck::Pod)]
            $vis struct $le_int_ty($base_ty);

            impl $le_int_ty{
                #[doc = concat!("Constructs an [`", stringify!($le_int_ty), "`] from it's base type. On big-endian platforms, this swaps the bytes of `x`")]
                $vis const fn new(x: $base_ty) -> Self{
                    Self(x.to_le())
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to it's base type. On big-endian platforms, this swaps the bytes of `x`")]
                $vis const fn get(self) -> $base_ty{
                    self.0.to_le()
                }


                #[doc = concat!("Constructs a [`", stringify!($le_int_ty), "`] from the raw LE bytes. This is zero cost on all platforms")]
                $vis const fn from_le_bytes(x: [u8;core::mem::size_of::<Self>()]) -> Self{
                    Self(<$base_ty>::from_ne_bytes(x))
                }

                #[doc = concat!("Constructs a [`", stringify!($le_int_ty), "`] from the raw BE bytes. This swaps bytes on all platforms")]
                $vis const fn from_be_bytes(x: [u8;core::mem::size_of::<Self>()]) -> Self{
                    Self(<$base_ty>::from_ne_bytes(x).swap_bytes())
                }

                #[doc = concat!("Constructs a [`", stringify!($le_int_ty), "`] from the raw bytes in native order. This swaps bytes on big-endian platforms\n",
                "This is equivalent to [`", stringify!($le_int_ty), "::new`] called with the result of [`", stringify!($base_ty),"::from_ne_bytes`]")]
                $vis const fn from_ne_bytes(x: [u8;core::mem::size_of::<Self>()]) -> Self{
                    Self(<$base_ty>::from_ne_bytes(x).to_le())
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to the raw LE bytes. This is zero cost on all platforms")]
                $vis const fn to_le_bytes(self) -> [u8;core::mem::size_of::<Self>()]{
                    self.0.to_ne_bytes()
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to the raw BE bytes. This swaps bytes on all platforms")]
                $vis const fn to_be_bytes(self) -> [u8;core::mem::size_of::<Self>()]{
                    self.0.swap_bytes().to_ne_bytes()
                }

                #[doc = concat!("Converts a [`", stringify!($le_int_ty), "`] to the raw bytes in native order. This swaps bytes on big-endian platforms")]
                $vis const fn to_ne_bytes(self) -> [u8;core::mem::size_of::<Self>()]{
                    self.0.to_le().to_ne_bytes()
                }

                $vis const fn truncate_to<T>(self) -> T where T: Truncate<Self>{
                    union Bytes<T: Copy>{
                        base: [u8;core::mem::size_of::<$le_int_ty>()],
                        interleave: T
                    }

                    let bytes = Bytes::<T>{
                        base: [0u8;core::mem::size_of::<Self>()]
                    };
                    unsafe{bytes.interleave}
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

            impl ::core::hash::Hash for $le_int_ty{
                fn hash<H: ::core::hash::Hasher>(&self, state: &mut H){
                    let val = self.get();
                    val.hash(state)
                }
            }

            impl ::core::cmp::PartialEq for $le_int_ty{
                #[inline]
                fn eq(&self, other: &Self) -> bool{
                    let this = self.get();
                    let other = other.get();

                    this == other
                }


            }
            impl ::core::cmp::Eq for $le_int_ty{}

            impl ::core::cmp::Ord for $le_int_ty{
                #[inline]
                fn cmp(&self, other: &Self) -> ::core::cmp::Ordering{
                    let this = self.get();
                    let other = other.get();

                    this.cmp(&other)
                }
            }

            impl ::core::cmp::PartialOrd for $le_int_ty{
                #[inline]
                fn partial_cmp(&self, other: &Self) -> Option<::core::cmp::Ordering>{
                    Some(self.cmp(other))
                }
            }

            impl ::core::cmp::PartialEq<$base_ty> for $le_int_ty{
                #[inline]
                fn eq(&self, other: &$base_ty) -> bool{
                    let this = self.get();
                    let other = *other;

                    this == other
                }
            }

            impl ::core::cmp::PartialEq<$le_int_ty> for $base_ty{
                #[inline]
                fn eq(&self, other: &$le_int_ty) -> bool{
                    let this = *self;
                    let other = other.get();

                    this == other
                }
            }

            impl ::core::cmp::PartialOrd<$base_ty> for $le_int_ty{
                #[inline]
                fn partial_cmp(&self, other: &$base_ty) -> Option<::core::cmp::Ordering>{
                    let this = self.get();
                    this.partial_cmp(other)
                }
            }

            impl ::core::cmp::PartialOrd<$le_int_ty> for $base_ty{
                #[inline]
                fn partial_cmp(&self, other: &$le_int_ty) -> Option<::core::cmp::Ordering>{
                    let other = other.get();
                    self.partial_cmp(&other)
                }
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

            impl ::core::ops::BitAnd for $le_int_ty{
                type Output = Self;
                #[inline]
                fn bitand(self, rhs: Self) -> Self{
                    Self(self.0&rhs.0)
                }
            }

            impl ::core::ops::BitOr for $le_int_ty{
                type Output = Self;
                #[inline]
                fn bitor(self, rhs: Self) -> Self{
                    Self(self.0&rhs.0)
                }
            }

            impl ::core::ops::BitXor for $le_int_ty{
                type Output = Self;
                #[inline]
                fn bitxor(self, rhs: Self) -> Self{
                    Self(self.0&rhs.0)
                }
            }

            impl ::core::ops::Not for $le_int_ty{
                type Output = Self;
                #[inline]
                fn not(self) -> Self{
                    Self(!self.0)
                }
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
                    <$unsigned_ty>::from_le_bytes(self.to_le_bytes())
                }
            }
            impl $unsigned_ty{
                pub const fn cast_sign(self) -> $signed_ty{
                    <$signed_ty>::from_le_bytes(self.to_le_bytes())
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

def_le_integers! {
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

use ark_ff::{
    biginteger::BigInteger320 as BigInteger,
    fields::{FftParameters, Fp320, Fp320Parameters, FpParameters},
};

pub type Fr = Fp320<FrParameters>;

pub struct FrParameters;

impl Fp320Parameters for FrParameters {}
impl FftParameters for FrParameters {
    type BigInt = BigInteger;

    const TWO_ADICITY: u32 = 1u32;

    // ROOT_OF_UNITY = GENERATOR ^ t =
    // 118980571542315331438337312413262112886281219744507561120271964887686106682370032123932630
    // t is defined below
    // This number needs to be in the Montgomery residue form.
    // I.e., write
    // 118980571542315331438337312413262112886281219744507561120271964887686106682370032123932630
    // * R
    // = 14596494758349247937872919467301196219547084259323651055171406111196152579418790325693086
    #[rustfmt::skip]
    const TWO_ADIC_ROOT_OF_UNITY: BigInteger = BigInteger([
        4913018085921565342u64,
        18164325898792356216u64,
        11499902056485864693u64,
        12113224729248979119u64,
        126057789046u64,
    ]);
}
impl FpParameters for FrParameters {
    // MODULUS = 118980571542315331438337312413262112886281219744507561120271964887686106682370032123932631
    // Factors of MODULUS - 1:
    //      2
    //      5
    //      17
    //      47
    //      3645289
    //      42373926857
    //      96404785755712297250936212793128201320333033128042968811755970858369
    #[rustfmt::skip]
    const MODULUS: BigInteger = BigInteger([
        15535567651727634391u64,
        14992835038329117496u64,
        12879083654034347181u64,
        16760578290609820963u64,
        1027536270620u64,
    ]);

    const MODULUS_BITS: u32 = 296;

    const CAPACITY: u32 = Self::MODULUS_BITS - 1;

    const REPR_SHAVE_BITS: u32 = 24;

    // see algebra-core/src/fields/mod.rs for more information
    // R = pow(2,320) %
    // 118980571542315331438337312413262112886281219744507561120271964887686106682370032123932631
    // R = 104384076783966083500464392945960916666734135485183910065100558776489954102951241798239545
    #[rustfmt::skip]
    const R: BigInteger = BigInteger([
        10622549565806069049u64,
        15275253213246312896u64,
        1379181597548482487u64,
        4647353561360841844u64,
        901478481574u64
    ]);

    // R2 = R * R %
    // 118980571542315331438337312413262112886281219744507561120271964887686106682370032123932631
    // R2 = 64940318866745953005690402896764745514897573584912026577721076893188083397226247459368768
    #[rustfmt::skip]
    const R2: BigInteger = BigInteger([
        16858329796171722560u64,
        12060416575249219689u64,
        17034911964548502611u64,
        14718631438675169669u64,
        560835539754u64
    ]);

    // INV = -(118980571542315331438337312413262112886281219744507561120271964887686106682370032123932631)^(-1) % 2^64
    const INV: u64 = 9223688842165816345u64;

    // GENERATOR = 7
    // This number needs to be in the Montgomery residue form.
    // I.e., write 7 * R =
    // 16805108233870595873226876142153739349451629929242003734072122109313038626438499844081029
    #[rustfmt::skip]
    const GENERATOR: BigInteger = BigInteger([
        18037929197695780229u64,
        16969762262749485294u64,
        6166745553471500787u64,
        5754981480705173590u64,
        145131747294u64,
    ]);

    // (n-1)/2 = 59490285771157665719168656206631056443140609872253780560135982443843053341185016061966315
    #[rustfmt::skip]
    const MODULUS_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        7767783825863817195u64,
        16719789556019334556u64,
        15662913863871949398u64,
        8380289145304910481u64,
        513768135310u64,
    ]);

    // t = (n - 1) / 2^{TWO_ADICITY} =
    // 59490285771157665719168656206631056443140609872253780560135982443843053341185016061966315
    const T: BigInteger = BigInteger([
        7767783825863817195u64,
        16719789556019334556u64,
        15662913863871949398u64,
        8380289145304910481u64,
        513768135310u64,
    ]);

    // (t-1)/2 = 29745142885578832859584328103315528221570304936126890280067991221921526670592508030983157
    const T_MINUS_ONE_DIV_TWO: BigInteger = BigInteger([
        3883891912931908597u64,
        8359894778009667278u64,
        17054828968790750507u64,
        4190144572652455240u64,
        256884067655u64,
    ]);
}

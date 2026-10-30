Theory vfmTest3064[no_sig_docs]
Ancestors vfmTestDefs3064
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3064_0.nsv", "result3064_1.nsv", "result3064_2.nsv", "result3064_3.nsv", "result3064_4.nsv", "result3064_5.nsv", "result3064_6.nsv", "result3064_7.nsv", "result3064_8.nsv", "result3064_9.nsv", "result3064_10.nsv", "result3064_11.nsv", "result3064_12.nsv", "result3064_13.nsv", "result3064_14.nsv", "result3064_15.nsv", "result3064_16.nsv", "result3064_17.nsv", "result3064_18.nsv", "result3064_19.nsv", "result3064_20.nsv", "result3064_21.nsv", "result3064_22.nsv", "result3064_23.nsv", "result3064_24.nsv", "result3064_25.nsv", "result3064_26.nsv", "result3064_27.nsv", "result3064_28.nsv", "result3064_29.nsv", "result3064_30.nsv", "result3064_31.nsv", "result3064_32.nsv", "result3064_33.nsv", "result3064_34.nsv", "result3064_35.nsv", "result3064_36.nsv", "result3064_37.nsv", "result3064_38.nsv", "result3064_39.nsv", "result3064_40.nsv", "result3064_41.nsv", "result3064_42.nsv", "result3064_43.nsv", "result3064_44.nsv", "result3064_45.nsv", "result3064_46.nsv", "result3064_47.nsv", "result3064_48.nsv", "result3064_49.nsv", "result3064_50.nsv", "result3064_51.nsv", "result3064_52.nsv", "result3064_53.nsv", "result3064_54.nsv", "result3064_55.nsv", "result3064_56.nsv", "result3064_57.nsv", "result3064_58.nsv", "result3064_59.nsv"];
val thyn = "vfmTestDefs3064";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

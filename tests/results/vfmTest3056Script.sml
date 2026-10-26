Theory vfmTest3056[no_sig_docs]
Ancestors vfmTestDefs3056
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3056_0.nsv", "result3056_1.nsv", "result3056_2.nsv", "result3056_3.nsv", "result3056_4.nsv", "result3056_5.nsv", "result3056_6.nsv", "result3056_7.nsv", "result3056_8.nsv", "result3056_9.nsv", "result3056_10.nsv", "result3056_11.nsv", "result3056_12.nsv", "result3056_13.nsv", "result3056_14.nsv", "result3056_15.nsv", "result3056_16.nsv", "result3056_17.nsv", "result3056_18.nsv", "result3056_19.nsv", "result3056_20.nsv", "result3056_21.nsv", "result3056_22.nsv", "result3056_23.nsv", "result3056_24.nsv", "result3056_25.nsv", "result3056_26.nsv", "result3056_27.nsv", "result3056_28.nsv", "result3056_29.nsv", "result3056_30.nsv", "result3056_31.nsv", "result3056_32.nsv", "result3056_33.nsv", "result3056_34.nsv", "result3056_35.nsv"];
val thyn = "vfmTestDefs3056";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

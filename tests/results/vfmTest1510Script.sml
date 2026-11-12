Theory vfmTest1510[no_sig_docs]
Ancestors vfmTestDefs1510
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1510_0.nsv", "result1510_1.nsv", "result1510_2.nsv", "result1510_3.nsv", "result1510_4.nsv", "result1510_5.nsv", "result1510_6.nsv", "result1510_7.nsv", "result1510_8.nsv", "result1510_9.nsv", "result1510_10.nsv", "result1510_11.nsv", "result1510_12.nsv", "result1510_13.nsv", "result1510_14.nsv", "result1510_15.nsv", "result1510_16.nsv", "result1510_17.nsv", "result1510_18.nsv", "result1510_19.nsv", "result1510_20.nsv", "result1510_21.nsv", "result1510_22.nsv", "result1510_23.nsv", "result1510_24.nsv", "result1510_25.nsv", "result1510_26.nsv", "result1510_27.nsv", "result1510_28.nsv", "result1510_29.nsv", "result1510_30.nsv", "result1510_31.nsv"];
val thyn = "vfmTestDefs1510";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

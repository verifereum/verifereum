Theory vfmTest1279[no_sig_docs]
Ancestors vfmTestDefs1279
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1279_0.nsv", "result1279_1.nsv", "result1279_2.nsv", "result1279_3.nsv", "result1279_4.nsv", "result1279_5.nsv", "result1279_6.nsv", "result1279_7.nsv", "result1279_8.nsv", "result1279_9.nsv", "result1279_10.nsv", "result1279_11.nsv", "result1279_12.nsv", "result1279_13.nsv", "result1279_14.nsv", "result1279_15.nsv", "result1279_16.nsv", "result1279_17.nsv", "result1279_18.nsv", "result1279_19.nsv", "result1279_20.nsv", "result1279_21.nsv", "result1279_22.nsv", "result1279_23.nsv", "result1279_24.nsv", "result1279_25.nsv", "result1279_26.nsv"];
val thyn = "vfmTestDefs1279";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest1096[no_sig_docs]
Ancestors vfmTestDefs1096
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1096_0.nsv", "result1096_1.nsv", "result1096_2.nsv", "result1096_3.nsv", "result1096_4.nsv", "result1096_5.nsv", "result1096_6.nsv", "result1096_7.nsv", "result1096_8.nsv", "result1096_9.nsv", "result1096_10.nsv", "result1096_11.nsv", "result1096_12.nsv", "result1096_13.nsv", "result1096_14.nsv", "result1096_15.nsv", "result1096_16.nsv", "result1096_17.nsv", "result1096_18.nsv", "result1096_19.nsv"];
val thyn = "vfmTestDefs1096";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

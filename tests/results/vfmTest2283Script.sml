Theory vfmTest2283[no_sig_docs]
Ancestors vfmTestDefs2283
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2283_0.nsv", "result2283_1.nsv", "result2283_2.nsv", "result2283_3.nsv", "result2283_4.nsv", "result2283_5.nsv", "result2283_6.nsv", "result2283_7.nsv", "result2283_8.nsv", "result2283_9.nsv", "result2283_10.nsv", "result2283_11.nsv", "result2283_12.nsv", "result2283_13.nsv", "result2283_14.nsv", "result2283_15.nsv"];
val thyn = "vfmTestDefs2283";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

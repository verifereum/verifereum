Theory vfmTest1628[no_sig_docs]
Ancestors vfmTestDefs1628
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1628_0.nsv", "result1628_1.nsv", "result1628_2.nsv", "result1628_3.nsv", "result1628_4.nsv", "result1628_5.nsv", "result1628_6.nsv", "result1628_7.nsv"];
val thyn = "vfmTestDefs1628";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

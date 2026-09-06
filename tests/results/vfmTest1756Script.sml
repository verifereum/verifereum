Theory vfmTest1756[no_sig_docs]
Ancestors vfmTestDefs1756
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1756_0.nsv", "result1756_1.nsv", "result1756_2.nsv", "result1756_3.nsv", "result1756_4.nsv", "result1756_5.nsv", "result1756_6.nsv", "result1756_7.nsv"];
val thyn = "vfmTestDefs1756";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

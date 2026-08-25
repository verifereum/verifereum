Theory vfmTest2832[no_sig_docs]
Ancestors vfmTestDefs2832
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2832_0.nsv", "result2832_1.nsv", "result2832_2.nsv", "result2832_3.nsv"];
val thyn = "vfmTestDefs2832";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

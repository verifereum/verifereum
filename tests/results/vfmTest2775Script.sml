Theory vfmTest2775[no_sig_docs]
Ancestors vfmTestDefs2775
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2775_0.nsv", "result2775_1.nsv", "result2775_2.nsv", "result2775_3.nsv"];
val thyn = "vfmTestDefs2775";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

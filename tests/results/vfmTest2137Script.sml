Theory vfmTest2137[no_sig_docs]
Ancestors vfmTestDefs2137
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2137_0.nsv", "result2137_1.nsv", "result2137_2.nsv", "result2137_3.nsv", "result2137_4.nsv", "result2137_5.nsv"];
val thyn = "vfmTestDefs2137";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

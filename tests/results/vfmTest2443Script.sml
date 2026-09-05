Theory vfmTest2443[no_sig_docs]
Ancestors vfmTestDefs2443
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2443_0.nsv", "result2443_1.nsv", "result2443_2.nsv", "result2443_3.nsv"];
val thyn = "vfmTestDefs2443";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

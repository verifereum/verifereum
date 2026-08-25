Theory vfmTest2639[no_sig_docs]
Ancestors vfmTestDefs2639
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2639_0.nsv", "result2639_1.nsv", "result2639_2.nsv", "result2639_3.nsv"];
val thyn = "vfmTestDefs2639";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

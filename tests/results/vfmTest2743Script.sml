Theory vfmTest2743[no_sig_docs]
Ancestors vfmTestDefs2743
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2743_0.nsv", "result2743_1.nsv", "result2743_2.nsv", "result2743_3.nsv"];
val thyn = "vfmTestDefs2743";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

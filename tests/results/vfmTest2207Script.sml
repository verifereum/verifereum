Theory vfmTest2207[no_sig_docs]
Ancestors vfmTestDefs2207
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2207_0.nsv", "result2207_1.nsv", "result2207_2.nsv"];
val thyn = "vfmTestDefs2207";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

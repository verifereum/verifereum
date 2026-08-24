Theory vfmTest2244[no_sig_docs]
Ancestors vfmTestDefs2244
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2244_0.nsv", "result2244_1.nsv"];
val thyn = "vfmTestDefs2244";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

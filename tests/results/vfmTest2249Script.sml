Theory vfmTest2249[no_sig_docs]
Ancestors vfmTestDefs2249
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2249_0.nsv", "result2249_1.nsv"];
val thyn = "vfmTestDefs2249";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

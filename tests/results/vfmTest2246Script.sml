Theory vfmTest2246[no_sig_docs]
Ancestors vfmTestDefs2246
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2246_0.nsv", "result2246_1.nsv"];
val thyn = "vfmTestDefs2246";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

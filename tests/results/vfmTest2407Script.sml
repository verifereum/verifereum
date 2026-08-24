Theory vfmTest2407[no_sig_docs]
Ancestors vfmTestDefs2407
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2407_0.nsv", "result2407_1.nsv"];
val thyn = "vfmTestDefs2407";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

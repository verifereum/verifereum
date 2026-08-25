Theory vfmTest2522[no_sig_docs]
Ancestors vfmTestDefs2522
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2522_0.nsv"];
val thyn = "vfmTestDefs2522";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

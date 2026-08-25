Theory vfmTest2386[no_sig_docs]
Ancestors vfmTestDefs2386
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2386_0.nsv"];
val thyn = "vfmTestDefs2386";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

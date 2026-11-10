Theory vfmTest2893[no_sig_docs]
Ancestors vfmTestDefs2893
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2893_0.nsv"];
val thyn = "vfmTestDefs2893";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

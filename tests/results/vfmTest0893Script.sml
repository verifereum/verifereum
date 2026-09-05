Theory vfmTest0893[no_sig_docs]
Ancestors vfmTestDefs0893
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0893_0.nsv", "result0893_1.nsv"];
val thyn = "vfmTestDefs0893";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

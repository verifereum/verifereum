Theory vfmTest0453[no_sig_docs]
Ancestors vfmTestDefs0453
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0453_0.nsv"];
val thyn = "vfmTestDefs0453";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

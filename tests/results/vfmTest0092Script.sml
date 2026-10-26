Theory vfmTest0092[no_sig_docs]
Ancestors vfmTestDefs0092
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0092_0.nsv"];
val thyn = "vfmTestDefs0092";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

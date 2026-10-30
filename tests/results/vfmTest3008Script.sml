Theory vfmTest3008[no_sig_docs]
Ancestors vfmTestDefs3008
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3008_0.nsv", "result3008_1.nsv"];
val thyn = "vfmTestDefs3008";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

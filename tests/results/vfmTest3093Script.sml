Theory vfmTest3093[no_sig_docs]
Ancestors vfmTestDefs3093
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3093_0.nsv"];
val thyn = "vfmTestDefs3093";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

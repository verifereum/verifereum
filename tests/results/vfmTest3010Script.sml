Theory vfmTest3010[no_sig_docs]
Ancestors vfmTestDefs3010
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3010_0.nsv"];
val thyn = "vfmTestDefs3010";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

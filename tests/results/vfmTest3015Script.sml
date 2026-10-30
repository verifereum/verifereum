Theory vfmTest3015[no_sig_docs]
Ancestors vfmTestDefs3015
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3015_0.nsv"];
val thyn = "vfmTestDefs3015";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

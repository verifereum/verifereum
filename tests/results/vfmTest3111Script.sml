Theory vfmTest3111[no_sig_docs]
Ancestors vfmTestDefs3111
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3111_0.nsv"];
val thyn = "vfmTestDefs3111";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

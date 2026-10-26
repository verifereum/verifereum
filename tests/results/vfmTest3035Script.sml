Theory vfmTest3035[no_sig_docs]
Ancestors vfmTestDefs3035
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3035_0.nsv"];
val thyn = "vfmTestDefs3035";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

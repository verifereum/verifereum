Theory vfmTest3022[no_sig_docs]
Ancestors vfmTestDefs3022
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3022_0.nsv"];
val thyn = "vfmTestDefs3022";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

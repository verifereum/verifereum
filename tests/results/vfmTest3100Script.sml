Theory vfmTest3100[no_sig_docs]
Ancestors vfmTestDefs3100
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3100_0.nsv"];
val thyn = "vfmTestDefs3100";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

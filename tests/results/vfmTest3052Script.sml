Theory vfmTest3052[no_sig_docs]
Ancestors vfmTestDefs3052
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3052_0.nsv", "result3052_1.nsv"];
val thyn = "vfmTestDefs3052";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

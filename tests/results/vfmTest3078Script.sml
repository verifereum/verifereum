Theory vfmTest3078[no_sig_docs]
Ancestors vfmTestDefs3078
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3078_0.nsv", "result3078_1.nsv"];
val thyn = "vfmTestDefs3078";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

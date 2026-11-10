Theory vfmTest3031[no_sig_docs]
Ancestors vfmTestDefs3031
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3031_0.nsv", "result3031_1.nsv", "result3031_2.nsv"];
val thyn = "vfmTestDefs3031";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

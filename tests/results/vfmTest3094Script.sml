Theory vfmTest3094[no_sig_docs]
Ancestors vfmTestDefs3094
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3094_0.nsv", "result3094_1.nsv", "result3094_2.nsv", "result3094_3.nsv"];
val thyn = "vfmTestDefs3094";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

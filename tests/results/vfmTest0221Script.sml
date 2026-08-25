Theory vfmTest0221[no_sig_docs]
Ancestors vfmTestDefs0221
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0221_0.nsv", "result0221_1.nsv", "result0221_2.nsv"];
val thyn = "vfmTestDefs0221";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

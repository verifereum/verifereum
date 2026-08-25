Theory vfmTest0369[no_sig_docs]
Ancestors vfmTestDefs0369
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0369_0.nsv", "result0369_1.nsv", "result0369_2.nsv", "result0369_3.nsv", "result0369_4.nsv"];
val thyn = "vfmTestDefs0369";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

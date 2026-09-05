Theory vfmTest0147[no_sig_docs]
Ancestors vfmTestDefs0147
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0147_0.nsv", "result0147_1.nsv", "result0147_2.nsv", "result0147_3.nsv"];
val thyn = "vfmTestDefs0147";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

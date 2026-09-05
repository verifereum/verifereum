Theory vfmTest0293[no_sig_docs]
Ancestors vfmTestDefs0293
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0293_0.nsv", "result0293_1.nsv", "result0293_2.nsv", "result0293_3.nsv", "result0293_4.nsv"];
val thyn = "vfmTestDefs0293";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0925[no_sig_docs]
Ancestors vfmTestDefs0925
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0925_0.nsv", "result0925_1.nsv", "result0925_2.nsv", "result0925_3.nsv", "result0925_4.nsv", "result0925_5.nsv", "result0925_6.nsv", "result0925_7.nsv", "result0925_8.nsv", "result0925_9.nsv"];
val thyn = "vfmTestDefs0925";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

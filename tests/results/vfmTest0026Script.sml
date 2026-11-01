Theory vfmTest0026[no_sig_docs]
Ancestors vfmTestDefs0026
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0026_0.nsv", "result0026_1.nsv", "result0026_2.nsv", "result0026_3.nsv", "result0026_4.nsv", "result0026_5.nsv", "result0026_6.nsv", "result0026_7.nsv", "result0026_8.nsv", "result0026_9.nsv"];
val thyn = "vfmTestDefs0026";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

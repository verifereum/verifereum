Theory vfmTest0349[no_sig_docs]
Ancestors vfmTestDefs0349
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0349_0.nsv", "result0349_1.nsv", "result0349_2.nsv", "result0349_3.nsv", "result0349_4.nsv", "result0349_5.nsv", "result0349_6.nsv", "result0349_7.nsv"];
val thyn = "vfmTestDefs0349";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

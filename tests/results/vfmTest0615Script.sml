Theory vfmTest0615[no_sig_docs]
Ancestors vfmTestDefs0615
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0615_0.nsv", "result0615_1.nsv", "result0615_2.nsv", "result0615_3.nsv", "result0615_4.nsv", "result0615_5.nsv", "result0615_6.nsv", "result0615_7.nsv", "result0615_8.nsv", "result0615_9.nsv", "result0615_10.nsv", "result0615_11.nsv"];
val thyn = "vfmTestDefs0615";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

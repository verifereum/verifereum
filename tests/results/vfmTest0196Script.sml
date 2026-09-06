Theory vfmTest0196[no_sig_docs]
Ancestors vfmTestDefs0196
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0196_0.nsv", "result0196_1.nsv", "result0196_2.nsv", "result0196_3.nsv", "result0196_4.nsv", "result0196_5.nsv", "result0196_6.nsv", "result0196_7.nsv"];
val thyn = "vfmTestDefs0196";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

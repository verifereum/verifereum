Theory vfmTest0890[no_sig_docs]
Ancestors vfmTestDefs0890
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0890_0.nsv", "result0890_1.nsv", "result0890_2.nsv", "result0890_3.nsv", "result0890_4.nsv", "result0890_5.nsv", "result0890_6.nsv", "result0890_7.nsv", "result0890_8.nsv", "result0890_9.nsv"];
val thyn = "vfmTestDefs0890";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

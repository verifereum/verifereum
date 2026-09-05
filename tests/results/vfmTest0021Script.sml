Theory vfmTest0021[no_sig_docs]
Ancestors vfmTestDefs0021
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0021_0.nsv", "result0021_1.nsv", "result0021_2.nsv", "result0021_3.nsv", "result0021_4.nsv", "result0021_5.nsv", "result0021_6.nsv", "result0021_7.nsv", "result0021_8.nsv", "result0021_9.nsv"];
val thyn = "vfmTestDefs0021";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

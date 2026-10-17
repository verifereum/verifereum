Theory vfmTest0720[no_sig_docs]
Ancestors vfmTestDefs0720
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0720_0.nsv", "result0720_1.nsv", "result0720_2.nsv", "result0720_3.nsv", "result0720_4.nsv", "result0720_5.nsv", "result0720_6.nsv", "result0720_7.nsv", "result0720_8.nsv", "result0720_9.nsv"];
val thyn = "vfmTestDefs0720";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

Theory vfmTest0014[no_sig_docs]
Ancestors vfmTestDefs0014
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0014_0.nsv", "result0014_1.nsv", "result0014_2.nsv", "result0014_3.nsv", "result0014_4.nsv", "result0014_5.nsv", "result0014_6.nsv", "result0014_7.nsv", "result0014_8.nsv", "result0014_9.nsv", "result0014_10.nsv", "result0014_11.nsv"];
val thyn = "vfmTestDefs0014";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

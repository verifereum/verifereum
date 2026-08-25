Theory vfmTest0856[no_sig_docs]
Ancestors vfmTestDefs0856
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0856_0.nsv", "result0856_1.nsv", "result0856_2.nsv", "result0856_3.nsv", "result0856_4.nsv", "result0856_5.nsv", "result0856_6.nsv", "result0856_7.nsv", "result0856_8.nsv", "result0856_9.nsv", "result0856_10.nsv", "result0856_11.nsv"];
val thyn = "vfmTestDefs0856";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

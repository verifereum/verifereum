Theory vfmTest0635[no_sig_docs]
Ancestors vfmTestDefs0635
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0635_0.nsv", "result0635_1.nsv", "result0635_2.nsv", "result0635_3.nsv", "result0635_4.nsv", "result0635_5.nsv", "result0635_6.nsv", "result0635_7.nsv"];
val thyn = "vfmTestDefs0635";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

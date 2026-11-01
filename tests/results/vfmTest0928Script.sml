Theory vfmTest0928[no_sig_docs]
Ancestors vfmTestDefs0928
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0928_0.nsv", "result0928_1.nsv", "result0928_2.nsv", "result0928_3.nsv", "result0928_4.nsv", "result0928_5.nsv", "result0928_6.nsv", "result0928_7.nsv", "result0928_8.nsv", "result0928_9.nsv"];
val thyn = "vfmTestDefs0928";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;

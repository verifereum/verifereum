Theory vfmTest0382[no_sig_docs]
Ancestors vfmTestDefs0382
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0382_0.nsv", "result0382_1.nsv", "result0382_2.nsv", "result0382_3.nsv", "result0382_4.nsv", "result0382_5.nsv", "result0382_6.nsv", "result0382_7.nsv"];
val thyn = "vfmTestDefs0382";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
